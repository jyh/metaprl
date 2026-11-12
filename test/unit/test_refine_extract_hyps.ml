(* The refiner's extracts of SEQUENTS WITH HYPOTHESES (refiner/refiner/refine.ml
   term_of_extract: upd_term and all_args).  When a theorem's extract is
   computed, each assumption's extract is a sequent, and upd_term rebuilds it
   on the hypotheses of the subgoal it closes before the rule's extract is
   applied: same-named hypotheses are kept, a hypothesis named differently is
   renamed to the subgoal's name in the conclusion, and the hypothesis types
   are the subgoal's.  An extract of another length, a context where the
   subgoal has a hypothesis (or the reverse), a context of another name, or an
   extract that is not a sequent is passed on unchanged.
   In a null refiner, one primitive rule
     simp:  <H>; x: 'A >- 'B   |-   <H> >- imp{'A; 'B}      extract lam{x. 'b['x]}
   written the way a sequent rule's extract has to be written to pass
   prim_rule: the assumption's extract is a sequent of the assumption's shape
   (<H>; x: 'A >- 'b<|H|>['x]) and the rule's extract a sequent of the goal's
   shape (<H> >- lam{x. 'b<|H|>['x]}).  Two derived theorems, each proved by
   simp and then the assumption itself (nth_hyp):
     t1:  x: c >- c         |-   >- imp{c; c}
     t2:  <J>; x: c >- c    |-   <J> >- imp{c; c}
   Each line prints extract_term of a theorem on one assumption extract.
   Pinned as it reads today. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let show_t t = Simple_print.SimplePrint.string_of_term t
let name = "test_refine_extract_hyps"
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

let simp =
  let a = sov "A" [ "H" ] [] and b = sov "B" [ "H" ] [] in
  let sub = seq [ ctx "H"; hyp "x" a ] b and goal = seq [ ctx "H" ] (imp a b) in
  let tac = create_rule build "simp" es [] (mterm [ sub ] goal) in
    prim_rule build "simp" es [] (mterm [ sub ] goal)
      [ seq [ ctx "H"; hyp "x" a ] (sov "b" [ "H" ] [ "x" ]) ]
      (seq [ ctx "H" ] (lam "x" (sov "b" [ "H" ] [ "x" ])));
    tac

let thm n goal assum =
  let s = sentinal_of_refiner (refiner_of_build build) in
  let subs, e1 = refine s (simp ra []) (mk_msequent goal [ assum ]) in
  let _, e2 = refine s (nth_hyp 0) (mk_msequent (msequent_goal (List.hd subs)) [ assum ]) in
    ignore (create_rule build n es [] (mterm [ assum ] goal) : prim_tactic);
    derived_rule build n es [] (mterm [ assum ] goal) () (compose e1 [ e2 ])

let () =
  thm "t1" (seq [] (imp c c)) (seq [ hyp "x" c ] c);
  thm "t2" (seq [ ctx "J" ] (imp c c)) (seq [ ctx "J"; hyp "x" c ] c)

let line what n arg =
  let r =
    match extract_term (refiner_of_build build) (opname n) [ arg ] with
    | t -> show_t t
    | exception RefineError (s, _) -> "refused (" ^ s ^ ")"
    | exception Invalid_argument s -> "Invalid_argument (" ^ s ^ ")"
  in
    Printf.printf "%-44s %s\n" what (String.concat " " (String.split_on_char '\n' r))

let () =
  line "t1, the subgoal's name x" "t1" (seq [ hyp "x" c ] (sov "e" [] [ "x" ]));
  line "t1, another name y" "t1" (seq [ hyp "y" c ] (sov "e" [] [ "y" ]));
  line "t1, another name and type y: d" "t1" (seq [ hyp "y" d ] (sov "e" [] [ "y" ]));
  line "t1, two hypotheses y, z" "t1" (seq [ hyp "y" c; hyp "z" c ] (sov "e" [] [ "y"; "z" ]));
  line "t1, no hypothesis" "t1" (seq [] (sov "e" [] []));
  line "t1, not a sequent" "t1" (sov "e" [] []);
  line "t1, a context where x is" "t1" (seq [ ctx "K" ] (sov "e" [ "K" ] []));
  line "t2, the subgoal's names J, x" "t2" (seq [ ctx "J"; hyp "x" c ] (sov "e" [ "J" ] [ "x" ]));
  line "t2, J and another name y" "t2" (seq [ ctx "J"; hyp "y" c ] (sov "e" [ "J" ] [ "y" ]));
  line "t2, another context K, y" "t2" (seq [ ctx "K"; hyp "y" c ] (sov "e" [ "K" ] [ "y" ]));
  line "t2, a hypothesis where J is" "t2" (seq [ hyp "w" c; hyp "y" c ] (sov "e" [] [ "w"; "y" ]))
