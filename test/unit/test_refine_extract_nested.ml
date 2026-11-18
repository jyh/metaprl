(* The refiner's extract of a theorem proved by a DERIVED rule
   (refiner/refiner/refine.ml get_proof on PDerived: delayed_rule's
   compute_ext and make_wildcard_ext_args).  When an extract walks into a
   derived rule's step, the rule's own extract is computed once on
   wildcard arguments, one per assumption: a sequent assumption gets its
   own hypotheses and a second-order variable over them as the
   conclusion ('ext_arg<|contexts|>[hyps]), any other assumption a bare
   second-order variable.  Only derived rules with no assumptions had
   reached it (2026-11-15 rank: unit tests, theory build, proof census).
   In a null refiner: simp, a sequent rule (as test_refine_extract_hyps
   has it), and pimp, the same rule on terms that are not sequents
   ('B |- imp{'A; 'B}, extract kk{'b}).  t1, t2 and n1 are proved by
   them; u1, u2 and m1 are the same theorems proved by t1, t2 and n1,
   so their extracts go through the wildcards.  Each line prints
   extract_term on one assumption extract; each u/m line equals its t/n
   line.  A wildcard missing a hypothesis variable, a context, or the
   sequent form makes the substitution refuse (the mutants).
   The expected file is the output of the code as written (2026-11-15),
   never typed. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let show_t t = Simple_print.SimplePrint.string_of_term t
let name = "test_refine_extract_nested"
let build = null_refiner name
let es = Rewrite.empty_args_spec
let ra = Rewrite.empty_rw_args
let mterm subs goal = List.fold_right (fun s acc -> Term_sig.MetaImplies (Term_sig.MetaTheorem s, acc)) subs (Term_sig.MetaTheorem goal)
let opname n = Opname.mk_opname n (op name)
let ctx c = Term_sig.Context (v c, [], [])
let hyp x t = Term_sig.Hypothesis (v x, t)
let sov x conts args = mk_so_var_term (v x) (List.map v conts) (List.map (fun a -> mk_var_term (v a)) args)
let seq hyps concl = mk_sequent_term { sequent_args = mk_xlist_term []; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }
let imp a b = mk_simple_term (op "imp") [ a; b ]
let lam x b = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] b ]
let c = mk_simple_term (op "c") []
let d = mk_simple_term (op "d") []

(* simp:  <H>; x: 'A >- 'B  |-  <H> >- imp{'A; 'B}, extract lam{x. 'b['x]} *)
let simp =
  let a = sov "A" [ "H" ] [] and b = sov "B" [ "H" ] [] in
  let sub = seq [ ctx "H"; hyp "x" a ] b and goal = seq [ ctx "H" ] (imp a b) in
  let tac = create_rule build "simp" es [] (mterm [ sub ] goal) in
    prim_rule build "simp" es [] (mterm [ sub ] goal)
      [ seq [ ctx "H"; hyp "x" a ] (sov "b" [ "H" ] [ "x" ]) ]
      (seq [ ctx "H" ] (lam "x" (sov "b" [ "H" ] [ "x" ])));
    tac

(* pimp:  'B  |-  imp{'A; 'B}, on terms that are not sequents, extract kk{'b} *)
let pimp =
  let a = sov "A" [] [] and b = sov "B" [] [] in
  let tac = create_rule build "pimp" es [] (mterm [ b ] (imp a b)) in
    prim_rule build "pimp" es [] (mterm [ b ] (imp a b)) [ sov "b" [] [] ] (mk_simple_term (op "kk") [ sov "b" [] [] ]);
    tac

let sentinal () = sentinal_of_refiner (refiner_of_build build)

(* A derived rule proved by base, then the assumption; its tactic is returned. *)
let thm n base goal assum =
  let s = sentinal () in
  let subs, e1 = refine s (base ra []) (mk_msequent goal [ assum ]) in
  let _, e2 = refine s (nth_hyp 0) (mk_msequent (msequent_goal (List.hd subs)) [ assum ]) in
  let tac = create_rule build n es [] (mterm [ assum ] goal) in
    derived_rule build n es [] (mterm [ assum ] goal) () (compose e1 [ e2 ]);
    tac

let show what n arg =
  let r =
    match extract_term (refiner_of_build build) (opname n) [ arg ] with
    | t -> show_t t
    | exception RefineError (s, _) -> "refused (" ^ s ^ ")"
    | exception Invalid_argument s -> "Invalid_argument (" ^ s ^ ")"
  in
    Printf.printf "%-28s %s\n" what (String.concat " " (String.split_on_char '\n' r))

let () =
  let t1 = thm "t1" simp (seq [] (imp c c)) (seq [ hyp "x" c ] c) in
  let t2 = thm "t2" simp (seq [ ctx "J" ] (imp c c)) (seq [ ctx "J"; hyp "x" c ] c) in
  let n1 = thm "n1" pimp (imp c c) c in
  (* the same theorems, proved by the derived ones *)
  ignore (thm "u1" t1 (seq [] (imp c c)) (seq [ hyp "x" c ] c) : prim_tactic);
  ignore (thm "u2" t2 (seq [ ctx "J" ] (imp c c)) (seq [ ctx "J"; hyp "x" c ] c) : prim_tactic);
  ignore (thm "m1" n1 (imp c c) c : prim_tactic);
    show "t1" "t1" (seq [ hyp "x" c ] (sov "e" [] [ "x" ]));
    show "u1 (by t1)" "u1" (seq [ hyp "x" c ] (sov "e" [] [ "x" ]));
    show "t2" "t2" (seq [ ctx "J"; hyp "x" c ] (sov "e" [ "J" ] [ "x" ]));
    show "u2 (by t2)" "u2" (seq [ ctx "J"; hyp "x" c ] (sov "e" [ "J" ] [ "x" ]));
    show "n1" "n1" (sov "e" [] []);
    show "m1 (by n1)" "m1" (sov "e" [] [])
