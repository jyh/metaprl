(* The refiner's conditional rewrites (refiner/refiner/refine.ml
   create_cond_rewrite, crwtactic, candthenrw, corelserw, crwaddr), which no
   unit test reached (2026-11-11 reach census: refine.ml 72 of 896 points).
   Random conditional rewrites  P --> Q  if S1, ..., Sn  are created in a
   null refiner (P, Q and the Si patterns over f{_;_}, g{_}, c and the
   variables 'a and 'b, with Q and the Si using only variables of P, and P
   never a bare variable), combined at random with candthenrw, corelserw and
   crwaddr (a subterm path), placed at a clause (0 = the conclusion, j =
   hypothesis j) and applied through crwtactic and refine to random
   sequents.  The subgoals are compared with a model:
     a rewrite gives a term and a list of conditions, or fails;
     candthenrw a b   a, then b on the result; conditions a's then b's
     corelserw a b    a, or b if a fails
     crwaddr p a      a at the subterm at path p; fails if p is not there
     at clause j, success gives the sequent with that clause rewritten,
     then for each condition, in order, the ORIGINAL sequent with its
     conclusion replaced by the condition (a rewritten hypothesis is not
     rewritten in these); failure or a missing clause is refused.
   crwtactic at assumption i is checked the same way on a goal c with one to
   three assumptions: the first subgoal has assumption i rewritten; each
   condition subgoal's goal is the REWRITTEN assumption with its conclusion
   replaced by the condition, and it keeps the original assumptions.
   Fixed cases (measured, 2026-11-11):
     - a rewrite whose result is physically its input (redex 'a, contractum
       'a) gives the sequent alone: its conditions are dropped;
     - an address that is not a clause address is refused (crwtactic needs
       a sequent clause);
     - an assumption number past the end is refused.
   Not covered: binders (so the free-variable check on conditions is not
   reached), parameters and addresses of the rewrites, crwhigher.
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

let state = ref 9090
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type p = C | G of p | F of p * p | V of string
let rec gen_closed depth = if depth = 0 || pick 3 = 0 then C else if pick 2 = 0 then G (gen_closed (depth - 1)) else F (gen_closed (depth - 1), gen_closed (depth - 1))
let rec gen_pat depth =
  match pick 6 with
  | 0 -> V "a" | 1 -> V "b"
  | 2 -> C
  | _ when depth = 0 -> C
  | 3 -> G (gen_pat (depth - 1))
  | _ -> F (gen_pat (depth - 1), gen_pat (depth - 1))
let rec gen_redex () = match gen_pat 2 with V _ -> gen_redex () | p -> p
let rec vars = function C -> [] | V x -> [ x ] | G a -> vars a | F (a, b) -> vars a @ vars b
let rec gen_over bound depth =
  match pick 5 with
  | 0 | 1 when bound <> [] -> V (List.nth bound (pick (List.length bound)))
  | _ when depth = 0 -> C
  | 2 -> G (gen_over bound (depth - 1))
  | 3 -> F (gen_over bound (depth - 1), gen_over bound (depth - 1))
  | _ -> C
let rec show = function C -> "c" | V x -> "'" ^ x | G a -> "g{" ^ show a ^ "}" | F (a, b) -> "f{" ^ show a ^ "; " ^ show b ^ "}"

type r = Prim of int | Then of r * r | Else of r * r | Addr of int list * r
let rec show_r prims = function
  | Prim k -> let p, q, s = prims.(k) in Printf.sprintf "(%s --> %s if [%s])" (show p) (show q) (String.concat "; " (List.map show s))
  | Then (a, b) -> "then(" ^ show_r prims a ^ ", " ^ show_r prims b ^ ")"
  | Else (a, b) -> "else(" ^ show_r prims a ^ ", " ^ show_r prims b ^ ")"
  | Addr (p, a) -> "addr[" ^ String.concat "." (List.map string_of_int p) ^ "](" ^ show_r prims a ^ ")"

(* the model *)
let rec matches env p t =
  match p, t with
  | V x, _ -> (match List.assoc_opt x env with Some u -> if u = t then Some env else None | None -> Some ((x, t) :: env))
  | C, C -> Some env
  | G p, G t -> matches env p t
  | F (p1, p2), F (t1, t2) -> (match matches env p1 t1 with Some env -> matches env p2 t2 | None -> None)
  | _ -> None
let rec inst env = function C -> C | V x -> List.assoc x env | G a -> G (inst env a) | F (a, b) -> F (inst env a, inst env b)
let rec model prims r t =
  match r with
  | Prim k -> let p, q, s = prims.(k) in Option.map (fun env -> inst env q, List.map (inst env) s) (matches [] p t)
  | Then (a, b) -> (match model prims a t with Some (t1, c1) -> Option.map (fun (t2, c2) -> t2, c1 @ c2) (model prims b t1) | None -> None)
  | Else (a, b) -> (match model prims a t with Some x -> Some x | None -> model prims b t)
  | Addr (path, a) ->
     let rec at path t =
       match path, t with
       | [], _ -> model prims a t
       | 1 :: path, G x -> Option.map (fun (x, c) -> G x, c) (at path x)
       | 1 :: path, F (x, y) -> Option.map (fun (x, c) -> F (x, y), c) (at path x)
       | 2 :: path, F (x, y) -> Option.map (fun (y, c) -> F (x, y), c) (at path y)
       | _ -> None in
     at path t

(* sequents: hypotheses and a conclusion *)
type s = p list * p
let clause_model prims r j ((hyps, concl) : s) : (s * p list) option =
  if j = 0 then Option.map (fun (t, c) -> (hyps, t), c) (model prims r concl)
  else if j > List.length hyps then None
  else Option.map (fun (t, c) -> (List.mapi (fun k h -> if k = j - 1 then t else h) hyps, concl), c) (model prims r (List.nth hyps (j - 1)))

(* the refiner *)
let op s = Opname.make_opname [ s ]
let rec term = function
  | C -> mk_simple_term (op "c") [] | G a -> mk_simple_term (op "g") [ term a ]
  | F (a, b) -> mk_simple_term (op "f") [ term a; term b ] | V x -> mk_so_var_term (Lm_symbol.add x) [] []
let rec back t =
  let { Term_sig.term_op; term_terms } = dest_term t in
  match Opname.dest_opname (dest_op term_op).Term_sig.op_name, List.map (fun b -> back (dest_bterm b).Term_sig.bterm) term_terms with
  | [ "c" ], [] -> C | [ "g" ], [ a ] -> G a | [ "f" ], [ a; b ] -> F (a, b) | _ -> failwith "back"
let seq ((hyps, concl) : s) =
  mk_sequent_term { sequent_args = mk_xlist_term [];
                    sequent_hyps = SeqHyp.of_list (List.mapi (fun k h -> Term_sig.Hypothesis (Lm_symbol.add ("x" ^ string_of_int k), term h)) hyps);
                    sequent_concl = term concl }
let back_seq t : s =
  let e = explode_sequent t in
  List.map (function Term_sig.Hypothesis (_, h) -> back h | Term_sig.Context _ -> failwith "back_seq") (SeqHyp.to_list e.sequent_hyps), back e.sequent_concl
let rec show_s ((hyps, concl) : s) = "<" ^ String.concat ", " (List.map show hyps) ^ " |- " ^ show concl ^ ">"

let build = null_refiner "test_refine_crw"
let count = ref 0
let crw (p, q, s) =
  incr count;
  match create_cond_rewrite build ("crw" ^ string_of_int !count) Rewrite.empty_args_spec [] (List.map term s) (term p) (term q) with
  | CondRW r -> r Rewrite.empty_rw_args [] | PrimRW _ -> failwith "prim"
let address l = TermAddr.make_address l
let path p = List.map (fun i -> Term_addr_sig.Subterm i) p
let rec to_crw crws = function
  | Prim k -> crws.(k)
  | Then (a, b) -> candthenrw (to_crw crws a) (to_crw crws b)
  | Else (a, b) -> corelserw (to_crw crws a) (to_crw crws b)
  | Addr (p, a) -> crwaddr (address (path p)) (to_crw crws a)
let at_clause j c = crwaddr (address [ Term_addr_sig.ClauseAddr j ]) c

(* goal and assumptions of each subgoal, or None when refused *)
let apply i c goal assums =
  match refine any_sentinal (crwtactic i c) (mk_msequent goal assums) with
  | sg, _ -> Some (List.map (fun m -> msequent_goal m, msequent_all_assums m) sg)
  | exception Refiner.Refiner.RefineError.RefineError _ -> None

let rec gen_r n depth =
  match pick 6 with
  | 0 | 1 | 2 -> if depth = 0 || pick 2 = 0 then Prim (pick n) else gen_r n depth
  | 3 when depth > 0 -> Then (gen_r n (depth - 1), gen_r n (depth - 1))
  | 4 when depth > 0 -> Else (gen_r n (depth - 1), gen_r n (depth - 1))
  | _ when depth > 0 -> Addr (List.init (1 + pick 2) (fun _ -> 1 + pick 2), gen_r n (depth - 1))
  | _ -> Prim (pick n)

let () =
  let nprims = 12 and combos = 150 and goals = 40 in
  let prims = Array.init nprims (fun _ ->
                  let p = gen_redex () in
                  let bound = List.sort_uniq compare (vars p) in
                  p, gen_over bound 2, List.init (pick 3) (fun _ -> gen_over bound 2)) in
  let crws = Array.map crw prims in
  let tried = ref 0 and agree = ref 0 and applied = ref 0 and conds = ref 0 and first = ref None in
  let tried_a = ref 0 and agree_a = ref 0 and applied_a = ref 0 in
  for _ = 1 to combos do
    let r = gen_r nprims 2 in
    let c = to_crw crws r in
    for k = 1 to goals do
      let s = List.init (pick 3) (fun _ -> gen_closed 3), gen_closed 3 in
      let j = pick (List.length (fst s) + 2) in
      (* every other goal puts, at the clause, an instance of the redex the
         combination tries first, at the path its addresses lead to *)
      let s =
        if k mod 2 = 1 then s
        else
          let rec place r = match r with
            | Prim k -> let p, _, _ = prims.(k) in inst (List.map (fun x -> x, gen_closed 2) (List.sort_uniq compare (vars p))) p
            | Then (a, _) | Else (a, _) -> place a
            | Addr (path, a) -> List.fold_right (fun i t -> if i = 1 then G t else F (gen_closed 1, t)) path (place a) in
          let t = place r in
          if j = 0 then fst s, t
          else if j <= List.length (fst s) then List.mapi (fun i h -> if i = j - 1 then t else h) (fst s), snd s
          else s in
      incr tried;
      let expect =
        Option.map (fun (s', cs) -> (s', []) :: List.map (fun cd -> (fst s, cd), []) cs) (clause_model prims r j s) in
      let got =
        Option.map (List.map (fun (g, a) -> back_seq g, List.map back_seq a)) (apply 0 (at_clause j c) (seq s) []) in
      (match expect with Some e -> incr applied; conds := !conds + List.length e - 1 | None -> ());
      if expect = got then incr agree
      else if !first = None then first := Some (Printf.sprintf "%s at clause %d of %s" (show_r prims r) j (show_s s));
      (* the same rewrite at assumption i of a goal c with 1-3 assumptions *)
      incr tried_a;
      let others = List.init (pick 3) (fun _ -> [], gen_closed 2) in
      let i = 1 + pick (List.length others + 1) in
      let assums = List.filteri (fun k _ -> k < i - 1) others @ [ s ] @ List.filteri (fun k _ -> k >= i - 1) others in
      let expect_a =
        Option.map (fun (s', cs) ->
            (([], C), List.mapi (fun k a -> if k = i - 1 then s' else a) assums)
            :: List.map (fun cd -> (fst s', cd), assums) cs) (clause_model prims r j s) in
      let got_a =
        Option.map (List.map (fun (g, a) -> (if is_sequent_term g then back_seq g else ([], back g)), List.map back_seq a))
          (apply i (at_clause j c) (term C) (List.map seq assums)) in
      (match expect_a with Some _ -> incr applied_a | None -> ());
      if expect_a = got_a then incr agree_a
      else if !first = None then first := Some (Printf.sprintf "assumption: %s at clause %d of %s" (show_r prims r) j (show_s s))
    done
  done;
  Printf.printf "%-52s %d of %d\n" "at a clause of the goal, as the model says" !agree !tried;
  Printf.printf "%-52s %d applied, %d conditions\n" "of which" !applied !conds;
  Printf.printf "%-52s %d of %d\n" "at a clause of assumption i, as the model says" !agree_a !tried_a;
  Printf.printf "%-52s %d applied\n" "of which" !applied_a;
  (match !first with Some s -> Printf.printf "first disagreement: %s\n" s | None -> ())

let show_got = function
  | None -> "refused"
  | Some sg -> String.concat " ; " (List.map (fun (g, a) -> (if is_sequent_term g then show_s (back_seq g) else show (back g)) ^ (if a = [] then "" else " with " ^ String.concat ", " (List.map (fun t -> show_s (back_seq t)) a))) sg)

let () =
  let same = crw (V "a", V "a", [ C ]) in
  let same_f = crw (F (V "a", V "b"), F (V "a", V "b"), [ C ]) in
  Printf.printf "%-52s %s\n" "'a --> 'a if c, at the conclusion" (show_got (apply 0 (at_clause 0 same) (seq ([], G C)) []));
  Printf.printf "%-52s %s\n" "f{'a;'b} --> f{'a;'b} if c, at the conclusion" (show_got (apply 0 (at_clause 0 same_f) (seq ([], F (C, C))) []));
  let unwrap = crw (G (V "a"), V "a", [ G C ]) in
  Printf.printf "%-52s %s\n" "a subterm address, not a clause" (show_got (apply 0 (crwaddr (address (path [ 1 ])) unwrap) (seq ([], G C)) []));
  Printf.printf "%-52s %s\n" "the null address" (show_got (apply 0 unwrap (seq ([], G C)) []));
  Printf.printf "%-52s %s\n" "assumption 2 of 1" (show_got (apply 2 (at_clause 0 unwrap) (term C) [ seq ([], G C) ]))
