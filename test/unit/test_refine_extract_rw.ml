(* The refiner's extracts and dependencies through REWRITE steps, and
   describe_extract (refiner/refiner/refine.ml), which test_refine_extract
   leaves out ("Not covered: ... rewrites' justifications") and no other
   test reached (2026-11-11 reach census: 222 of refine.ml's 657 points
   reached by nothing; the rewrite-justification walk, the subgoal count
   behind a rewrite step, and describe_extract among them).
   In a null refiner: primitive rules with extracts
     ax  |- c                  extract k
     gi  'a |- g{'a}           extract q{'x}
     fi  'a, 'b |- f{'a; 'b}   extract p{'x; 'y}
   and primitive rewrites  ff: f{'a; 'a} --> g{'a}  and  gg: g{g{'a}} --> g{'a}.
   Each theorem below is proved by ONE rewrite step on its goal, then the
   primitives, and justified with derived_rule.  The line prints, for the
   rewrite step: describe_extract of its extract; for the theorem: its
   extract (extract_term), and compute_dependencies (sorted).  The
   rewrite forms: plain, at an address (rwaddr), composed (andthenrw),
   or-else (orelserw, first failing), and rwhigher; then describe_extract
   of a rule step, nth_hyp, a cut, an identity and a composition.
   Model: a rewrite changes the goal but not the extract, so the extract
   is the extract of the rewritten goal's primitive proof; the
   dependencies are the primitives used plus every rewrite named in the
   step.  Pinned as it reads today, including one inaccuracy: for
   rwhigher, the justification keeps no addresses, so describe_extract
   names the address of the term rwhigher was applied to, not the subterm
   the rewrite fired at (and None when it fired at two). *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

type p = C | G of p | F of p * p
let op s = Opname.make_opname [ s ]
let rec term = function
  | C -> mk_simple_term (op "c") [] | G a -> mk_simple_term (op "g") [ term a ] | F (a, b) -> mk_simple_term (op "f") [ term a; term b ]
let rec show = function C -> "c" | G a -> "g{" ^ show a ^ "}" | F (a, b) -> "f{" ^ show a ^ "; " ^ show b ^ "}"
let show_t t = Simple_print.SimplePrint.string_of_term t
let sv x = mk_so_var_term (Lm_symbol.add x) [] []

let name = "test_refine_extract_rw"
let build = null_refiner name
let es = Rewrite.empty_args_spec
let ra = Rewrite.empty_rw_args
let mterm subs goal = List.fold_right (fun s acc -> Term_sig.MetaImplies (Term_sig.MetaTheorem s, acc)) subs (Term_sig.MetaTheorem goal)
let opname n = Opname.mk_opname n (op name)
let prim n subs goal args ext =
  let tac = create_rule build n es [] (mterm subs goal) in
  prim_rule build n es [] (mterm subs goal) args ext; tac
let ax = prim "ax" [] (term C) [] (mk_simple_term (op "k") [])
let gi = prim "gi" [ sv "a" ] (mk_simple_term (op "g") [ sv "a" ]) [ sv "x" ] (mk_simple_term (op "q") [ sv "x" ])
let fi = prim "fi" [ sv "a"; sv "b" ] (mk_simple_term (op "f") [ sv "a"; sv "b" ]) [ sv "x"; sv "y" ] (mk_simple_term (op "p") [ sv "x"; sv "y" ])
let mkrw n redex contractum =
  match create_rewrite build n redex contractum with
  | PrimRW r -> prim_rewrite build n redex contractum; r
  | CondRW _ -> failwith "cond"
let ff = mkrw "ff" (mk_simple_term (op "f") [ sv "a"; sv "a" ]) (mk_simple_term (op "g") [ sv "a" ])
let gg = mkrw "gg" (mk_simple_term (op "g") [ mk_simple_term (op "g") [ sv "a" ] ]) (mk_simple_term (op "g") [ sv "a" ])

let sent () = sentinal_of_refiner (refiner_of_build build)
(* prove a closed pattern with the primitives *)
let rec prove s p =
  let _, ext = refine s ((match p with C -> ax | G _ -> gi | F _ -> fi) ra []) (mk_msequent (term p) []) in
  compose ext (List.map (prove s) (match p with C -> [] | G a -> [ a ] | F (a, b) -> [ a; b ]))
let rec model = function C -> "k" | G a -> "q{" ^ model a ^ "}" | F (a, b) -> "p{" ^ model a ^ "; " ^ model b ^ "}"
let rec back t =
  let { Term_sig.term_op; term_terms } = dest_term t in
  match Opname.dest_opname (dest_op term_op).Term_sig.op_name, List.map (fun b -> back (dest_bterm b).Term_sig.bterm) term_terms with
  | [ "c" ], [] -> C | [ "g" ], [ a ] -> G a | [ "f" ], [ a; b ] -> F (a, b) | _ -> failwith "back"

let describe e =
  let addr a = "[" ^ TermAddr.string_of_address a ^ "]" in
  let ed (o, ints, addrs, ts) = Printf.sprintf "%s ints [%s] addrs [%s] terms [%s]" (List.hd (Opname.dest_opname o))
      (String.concat ";" (List.map string_of_int ints)) (String.concat ";" (List.map addr addrs)) (String.concat ";" (List.map show_t ts)) in
  match describe_extract e with
  | EDRule a -> "EDRule " ^ ed a
  | EDRewrite None -> "EDRewrite None"
  | EDRewrite (Some (o, i, a)) -> Printf.sprintf "EDRewrite %s%s at %s" (List.hd (Opname.dest_opname o)) (if i = 0 then "" else Printf.sprintf " assum %d" i) (addr a)
  | EDCondRewrite None -> "EDCondRewrite None"
  | EDCondRewrite (Some (a, i, at)) -> "EDCondRewrite " ^ ed a ^ (if i = 0 then "" else Printf.sprintf " assum %d" i) ^ " at " ^ addr at
  | EDComposition -> "EDComposition"
  | EDNthHyp i -> "EDNthHyp " ^ string_of_int i
  | EDCut t -> "EDCut " ^ show_t t
  | EDIdentity -> "EDIdentity"

let deps n = String.concat " " (List.sort_uniq compare (List.map (fun (_, o) -> List.hd (Opname.dest_opname o)) (compute_dependencies (refiner_of_build build) (opname n))))

let count = ref 0
let theorem label goal rw =
  incr count;
  let n = "thm" ^ string_of_int !count in
  let s = sent () in
  match refine s (rwtactic 0 rw) (mk_msequent (term goal) []) with
  | exception RefineError.RefineError _ -> Printf.printf "%-40s %s: the rewrite is refused\n" label (show goal)
  | [ sub ], step ->
      let p = back (msequent_goal sub) in
      ignore (create_rule build n es [] (mterm [] (term goal)) : prim_tactic);
      derived_rule build n es [] (mterm [] (term goal)) () (compose step [ prove s p ]);
      let ext = try show_t (extract_term (refiner_of_build build) (opname n) []) with e -> "raised " ^ Printexc.to_string e in
      Printf.printf "%-40s %s -> %s\n   step: %s\n   extract %s (model %s)\n   dependencies %s\n" label (show goal) (show p) (describe step) ext (model p) (deps n)
  | subs, _ -> Printf.printf "%-40s %d subgoals\n" label (List.length subs)

let () =
  let addr l = TermAddr.make_address (List.map (fun i -> Term_addr_sig.Subterm i) l) in
  theorem "ff" (F (C, C)) ff;
  theorem "ff at [1]" (G (F (C, C))) (rwaddr (addr [ 1 ]) ff);
  theorem "ff at [2] of f" (F (C, F (G C, G C))) (rwaddr (addr [ 2 ]) ff);
  theorem "ff andthen gg" (F (G C, G C)) (andthenrw ff gg);
  theorem "gg orelse ff (gg fails)" (F (C, C)) (orelserw gg ff);
  theorem "ff orelse gg (ff succeeds)" (F (C, C)) (orelserw ff gg);
  theorem "rwhigher ff" (G (F (C, C))) (rwhigher ff);
  theorem "rwhigher ff, two redexes" (F (F (C, C), F (C, C))) (rwhigher ff);
  theorem "rwhigher ff, two redexes below the root" (F (G (F (C, C)), F (C, C))) (rwhigher ff);
  theorem "ff on a goal it does not match" (G C) ff;
  (* a rewrite step left open inside a composition, closed by a second one:
     the rule g{c} --> g{f{c; c}}, proved by (gi then ff), then nth_hyp 0 *)
  (let n = "open_rw" in
   let s = sent () in
   let goal = term (G (F (C, C))) and sub = term (G C) in
   ignore (create_rule build n es [] (mterm [ sub ] goal) : prim_tactic);
   let _, gext = refine s (gi ra []) (mk_msequent goal [ sub ]) in
   let _, rext = refine s (rwtactic 0 ff) (mk_msequent (term (F (C, C))) [ sub ]) in
   let _, hext = refine s (nth_hyp 0) (mk_msequent sub [ sub ]) in
   derived_rule build n es [] (mterm [ sub ] goal) () (compose (compose gext [ rext ]) [ hext ]);
   Printf.printf "%-40s %s\n   dependencies %s\n" "g{c} --> g{f{c; c}}: gi, ff, then nth_hyp"
     (try "extract with 'e for the subgoal: " ^ show_t (extract_term (refiner_of_build build) (opname n) [ sv "e" ]) with e -> "raised " ^ Printexc.to_string e)
     (deps n));
  (* describe_extract of the other step kinds *)
  let s = sent () in
  let show_step label f = Printf.printf "%-40s %s\n" label (try describe (f ()) with e -> "raised " ^ Printexc.to_string e) in
  show_step "a rule step (gi)" (fun () -> snd (refine s (gi ra []) (mk_msequent (term (G C)) [])));
  show_step "nth_hyp 0" (fun () -> snd (refine s (nth_hyp 0) (mk_msequent (term C) [ term C ])));
  show_step "cut g{c}" (fun () -> snd (refine s (cut (term (G C))) (mk_msequent (term C) [])));
  show_step "identity" (fun () -> identity s (mk_msequent (term C) []));
  show_step "a composition (gi then ax)" (fun () -> prove s (G C))
