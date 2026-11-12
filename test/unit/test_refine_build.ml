(* How the refiner is built and checked (refiner/refiner/refine.ml
   definitional_rewrite and its checks, justify_rewrite / prim_rewrite,
   prim_cond_rewrite, create_ml_rule, create_ml_rewrite, label_refiner,
   join_refiner, find_sentinal, sentinal_of_refiner, and the check of a
   primitive rule's extract arguments, check_subgoal_arg), which only the
   proof census reached (2026-11-11 reach census: 105 lines of refine.ml
   reached by the census and by no unit test).
   Every case is fixed; the outcome printed is the one the code gives
   (measured 2026-11-11), with the refusal's own message.
   Fixed cases:
     definitions: a definition d{'a; x.'b['x]} --> f{'a; 'b[c]} is accepted
       and rewrites under a sentinel of its refiner; a redex subterm that is
       not a second-order variable, a second-order argument that is not a
       variable, one that is not bound there, and a recursive contractum are
       each refused; two definitions of one shape in one refiner are
       accepted one at a time and refused when a sentinel is taken;
     rewrites: a rewrite created but not justified is refused by a sentinel
       of its refiner, and accepted by one taken after prim_rewrite;
       prim_rewrite of a name never created, or with another contractum, is
       refused; the same for conditional rewrites;
     joined refiners: a sentinel of a refiner that joined another (through
       its label) accepts the rules of both, and a sentinel of the other
       refuses the joiner's rule; a refiner joined twice is inserted once
       (its definition is not seen twice); find_sentinal of a rule gives the
       sentinel of what was there when the rule was justified (the rule
       itself is not in it), finds a rule through a join, refuses an ML
       rule, and raises Not_found for a name it does not have; ML rules and
       ML rewrites are accepted by a sentinel of their refiner;
     extract arguments (prim_rule, for each subgoal): over a sequent the
       argument must name every context and hypothesis variable in scope,
       and no context that is not, and carry the same sequent argument;
       elsewhere it must have the subgoal's operator and binder counts.  The general sequent argument passes the
       check and the rule is then refused when its extract is compiled (the
       context H is free in the result 'e<|H|>[c] outside the sequent):
       the test reaches the check, and no sequent rule here has a working
       extract.
   Not covered: delayed and derived rewrites (their extracts), input forms,
   the VERBOSE_EXN debug prints. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let mk s ts = mk_simple_term (op s) ts
let c = mk "c" []
let g x = mk "g" [ x ]
let f x y = mk "f" [ x; y ]
let sov ?(conts = []) x args = mk_so_var_term (v x) (List.map v conts) args
let var x = mk_var_term (v x)
let bind name bvars t = mk_term (mk_op (op name) []) [ mk_bterm (List.map v bvars) t ]
let show t = String.concat " " (List.filter (( <> ) "") (List.map String.trim (String.split_on_char '\n' (Simple_print.SimplePrint.string_of_term t))))

let rec msg = function
  | StringError s -> s
  | StringTermError (s, t) -> s ^ ": " ^ show t
  | StringStringError (s, t) -> s ^ ": " ^ t
  | RewriteFreeSOVar x -> "RewriteFreeSOVar " ^ Lm_symbol.to_string x
  | StringErrorError (s, e) -> s ^ ": " ^ msg e
  | StringVarError (s, x) -> s ^ ": " ^ Lm_symbol.to_string x
  | RewriteFreeContextVar (x, y) -> "RewriteFreeContextVar " ^ Lm_symbol.to_string x ^ " " ^ Lm_symbol.to_string y
  | RewriteMissingContextArg x -> "RewriteMissingContextArg " ^ Lm_symbol.to_string x
  | RewriteSOVarArity x -> "RewriteSOVarArity " ^ Lm_symbol.to_string x
  | RewriteStringError s -> s
  | VarError x -> "VarError " ^ Lm_symbol.to_string x
  | StringWrapError (s, e) -> s ^ ": " ^ msg e
  | VarErrorError (x, e) -> Lm_symbol.to_string x ^ ": " ^ msg e
  | _ -> "(another refine_error)"
let attempt label fn =
  Printf.printf "%-60s %s\n%!" label
    (try fn () with
     | RefineError (n, e) -> "refused (" ^ n ^ ": " ^ msg e ^ ")"
     | Invalid_argument s -> "Invalid_argument " ^ s
     | Not_found -> "Not_found"
     | Failure s -> "Failure " ^ s)

(* the result of rewriting [t] with [rw] under [sent], or the refusal *)
let rewrite sent rw t =
  match refine sent (rwtactic 0 rw) (mk_msequent t []) with
  | [ m ], _ -> "rewrites to " ^ show (msequent_goal m)
  | _, _ -> "several subgoals"
let prim = function PrimRW r -> r | CondRW _ -> failwith "cond"
let sentinel b = sentinal_of_refiner (refiner_of_build b)

(* a rule  c --> name{c}  with a primitive extract, and how it applies *)
let rule b name =
  let mt = Term_sig.MetaImplies (Term_sig.MetaTheorem c, Term_sig.MetaTheorem (mk name [ c ])) in
  let tac = create_rule b name Rewrite.empty_args_spec [] mt in
  prim_rule b name Rewrite.empty_args_spec [] mt [ sov "e" [] ] (sov "e" []);
  tac
let applies sent tac name =
  match refine sent (tac Rewrite.empty_rw_args []) (mk_msequent (mk name [ c ]) []) with
  | _ -> "accepted"
  | exception RefineError _ -> "refused"

let definitions () =
  let b = null_refiner "test_refine_build_def" in
  let redex = mk_term (mk_op (op "d") []) [ mk_bterm [] (sov "a" []); mk_bterm [ v "x" ] (sov "b" [ var "x" ]) ] in
  let contractum = f (sov "a" []) (sov "b" [ c ]) in
  let rw = prim (create_rewrite b "d" redex contractum) in
  attempt "definition d{'a; x.'b['x]} --> f{'a; 'b[c]}" (fun () -> definitional_rewrite b "d" redex contractum; "accepted");
  attempt "  under a sentinel, d{c; x.g{'x}}" (fun () ->
      rewrite (sentinel b) rw (mk_term (mk_op (op "d") []) [ mk_bterm [] c; mk_bterm [ v "x" ] (g (var "x")) ]));
  attempt "a redex subterm that is not a second-order variable" (fun () -> definitional_rewrite b "d2" (mk "d2" [ c ]) c; "accepted");
  attempt "a second-order argument that is not a variable" (fun () ->
      definitional_rewrite b "d3" (bind "d3" [ "x" ] (sov "b" [ c ])) c; "accepted");
  attempt "a second-order argument not bound there" (fun () ->
      definitional_rewrite b "d4" (bind "d4" [ "x" ] (sov "b" [ var "y" ])) c; "accepted");
  attempt "a recursive contractum d5{'a} --> g{d5{'a}}" (fun () ->
      definitional_rewrite b "d5" (mk "d5" [ sov "a" [] ]) (g (mk "d5" [ sov "a" [] ])); "accepted");
  (* the same shape twice, in a refiner of its own *)
  let b2 = null_refiner "test_refine_build_twice" in
  let r1 = mk "e" [ sov "a" [] ] and r2 = mk "e" [ sov "z" [] ] in
  ignore (create_rewrite b2 "e1" r1 (g (sov "a" [])));
  ignore (create_rewrite b2 "e2" r2 (f (sov "z" []) c));
  attempt "two definitions of e{_}: the first" (fun () -> definitional_rewrite b2 "e1" r1 (g (sov "a" [])); "accepted");
  attempt "  the second" (fun () -> definitional_rewrite b2 "e2" r2 (f (sov "z" []) c); "accepted");
  attempt "  a sentinel of that refiner" (fun () -> ignore (sentinel b2); "taken")

let rewrites () =
  let b = null_refiner "test_refine_build_rw" in
  let rw = prim (create_rewrite b "ung" (g (sov "a" [])) (sov "a" [])) in
  attempt "a rewrite created, not justified, under its sentinel" (fun () -> rewrite (sentinel b) rw (g c));
  attempt "  under a sentinel taken after prim_rewrite" (fun () ->
      prim_rewrite b "ung" (g (sov "a" [])) (sov "a" []); rewrite (sentinel b) rw (g c));
  attempt "prim_rewrite of a name never created" (fun () -> prim_rewrite b "never" (g (sov "a" [])) (sov "a" []); "accepted");
  attempt "prim_rewrite with another contractum" (fun () ->
      ignore (create_rewrite b "ung2" (g (sov "a" [])) (sov "a" []));
      prim_rewrite b "ung2" (g (sov "a" [])) c; "accepted");
  let seq concl = mk_sequent_term { TermType.sequent_args = mk_xlist_term []; sequent_hyps = SeqHyp.of_list []; sequent_concl = concl } in
  let crw = match create_cond_rewrite b "cung" Rewrite.empty_args_spec [] [] (g (sov "a" [])) (sov "a" []) with
    | CondRW r -> r Rewrite.empty_rw_args [] | PrimRW _ -> failwith "prim" in
  let capply sent = match refine sent (crwtactic 0 (crwaddr (TermAddr.make_address [ Term_addr_sig.ClauseAddr 0 ]) crw)) (mk_msequent (seq (g c)) []) with
    | [ m ], _ -> "rewrites to " ^ show (explode_sequent (msequent_goal m)).sequent_concl
    | l, _ -> string_of_int (List.length l) ^ " subgoals" in
  attempt "a conditional rewrite created, not justified" (fun () -> capply (sentinel b));
  attempt "  after prim_cond_rewrite" (fun () -> prim_cond_rewrite b "cung" [] [] (g (sov "a" [])) (sov "a" []); capply (sentinel b));
  attempt "prim_cond_rewrite of a name never created" (fun () -> prim_cond_rewrite b "cnever" [] [] (g (sov "a" [])) (sov "a" []); "accepted");
  attempt "prim_cond_rewrite with other conditions" (fun () ->
      ignore (create_cond_rewrite b "cung2" Rewrite.empty_args_spec [] [] (g (sov "a" [])) (sov "a" []));
      prim_cond_rewrite b "cung2" [] [ c ] (g (sov "a" [])) (sov "a" []); "accepted")

let joins () =
  let a = null_refiner "test_refine_build_a" in
  let ra = rule a "ra" in
  ignore (create_rewrite a "da" (mk "da" [ sov "x" [] ]) (g (sov "x" [])));
  definitional_rewrite a "da" (mk "da" [ sov "x" [] ]) (g (sov "x" []));
  let la = label_refiner a "A" in
  let b = null_refiner "test_refine_build_b" in
  join_refiner b la;
  let rb = rule b "rb" in
  let sb = sentinel b and sa = sentinel a in
  attempt "a sentinel of B (which joined A): A's rule" (fun () -> applies sb ra "ra");
  attempt "  B's rule" (fun () -> applies sb rb "rb");
  attempt "a sentinel of A: B's rule" (fun () -> applies sa rb "rb");
  let d = null_refiner "test_refine_build_d" in
  join_refiner d la;
  join_refiner d la;
  attempt "a refiner that joined A twice: a sentinel" (fun () -> applies (sentinel d) ra "ra");
  let opn s n = Opname.make_opname [ n; s ] in
  attempt "find_sentinal rb in B: rb" (fun () -> applies (find_sentinal (refiner_of_build b) (opn "test_refine_build_b" "rb")) rb "rb");
  attempt "  ra" (fun () -> applies (find_sentinal (refiner_of_build b) (opn "test_refine_build_b" "rb")) ra "ra");
  attempt "find_sentinal ra in B (through the join): ra" (fun () ->
      applies (find_sentinal (refiner_of_build b) (opn "test_refine_build_a" "ra")) ra "ra");
  attempt "find_sentinal of a name B does not have" (fun () -> ignore (find_sentinal (refiner_of_build b) (opn "test_refine_build_b" "zz")); "found");
  let m = null_refiner "test_refine_build_ml" in
  let mlr _ mseq _ = [ mseq ], (fun _ _ _ _ _ fs -> match fs with [ h ] -> h [] | _ -> c) in
  let mtac = create_ml_rule m "mlr" mlr in
  let mrw = prim (create_ml_rewrite m "mlrw" (fun t -> if alpha_equal t (g c) then c else raise (RefineError ("mlrw", StringError "no")))) in
  attempt "an ML rule under a sentinel of its refiner" (fun () ->
      match refine (sentinel m) (mtac Rewrite.empty_rw_args []) (mk_msequent c []) with _ -> "accepted");
  attempt "an ML rewrite under a sentinel of its refiner" (fun () -> rewrite (sentinel m) mrw (g c));
  attempt "find_sentinal of an ML rule" (fun () -> ignore (find_sentinal (refiner_of_build m) (opn "test_refine_build_ml" "mlr")); "found")

let extract_args () =
  let b = null_refiner "test_refine_build_ext" in
  let count = ref 0 in
  let seq ?(arg = c) hyps concl =
    mk_sequent_term { TermType.sequent_args = arg;
                      sequent_hyps = SeqHyp.of_list (Term_sig.Context (v "H", [], []) :: List.map (fun (x, t) -> Term_sig.Hypothesis (v x, t)) hyps);
                      sequent_concl = concl } in
  let try_rule label sub goal arg result =
    incr count;
    let name = "x" ^ string_of_int !count in
    let mt = Term_sig.MetaImplies (Term_sig.MetaTheorem sub, Term_sig.MetaTheorem goal) in
    attempt label (fun () ->
        ignore (create_rule b name Rewrite.empty_args_spec [] mt : prim_tactic);
        prim_rule b name Rewrite.empty_args_spec [] mt [ arg ] result; "accepted") in
  let sub = seq [ "x", mk "a" [] ] (mk "b" []) and goal = seq [] (f (mk "a" []) (mk "b" [])) in
  let res = mk "lam" [ sov ~conts:[ "H" ] "e" [ c ] ] in
  try_rule "sequent subgoal, argument 'e<|H|>['x] (passes the check)" sub goal (seq [ "x", mk "a" [] ] (sov ~conts:[ "H" ] "e" [ var "x" ])) res;
  try_rule "  'e<|H|>[] (x not named)" sub goal (seq [ "x", mk "a" [] ] (sov ~conts:[ "H" ] "e" [])) res;
  try_rule "  'e<||>['x] (H not named)" sub goal (seq [ "x", mk "a" [] ] (sov "e" [ var "x" ])) (mk "lam" [ sov "e" [ c ] ]);
  try_rule "  'e<|H; K|>['x] (K not in scope)" sub goal (seq [ "x", mk "a" [] ] (sov ~conts:[ "H"; "K" ] "e" [ var "x" ])) res;
  try_rule "  'e<|H|>['x; 'x] (x named twice)" sub goal (seq [ "x", mk "a" [] ] (sov ~conts:[ "H" ] "e" [ var "x"; var "x" ])) res;
  try_rule "  another sequent argument" sub goal (seq ~arg:(mk "other" []) [ "x", mk "a" [] ] (sov ~conts:[ "H" ] "e" [ var "x" ])) res;
  try_rule "term subgoal g{c}, argument g{'e}" (g c) (f c c) (g (sov "e" [])) (sov "e" []);
  try_rule "  f{'e; 'e}" (g c) (f c c) (f (sov "e" []) (sov "e" [])) (sov "e" []);
  try_rule "term subgoal lam{x.c}, argument lam{'e}" (bind "lam" [ "x" ] c) (g c) (mk "lam" [ sov "e" [] ]) (sov "e" [])

let () =
  definitions ();
  rewrites ();
  joins ();
  extract_args ()
