(* Unify_mm (refiner/reflib) unifies sequents as well as ordinary terms:
   my_dest_term views a sequent as one function symbol (FunSequent) whose
   arguments are the sequent's args and its body (hypotheses and
   conclusion, nested), and my_mk_term rebuilds a sequent from that view
   when a substitution or a solved equation needs one.  JProver unifies
   sequents this way.  No unit test reached that view (test_unify_mm uses
   f, g, c and lam only).

   This test unifies pairs of sequents and prints, for each pair, whether
   Unify_mm.unifiable and Unify_mm.unify agree, the substitution unify
   returns (sorted by variable), and whether every value it binds that is
   a sequent is one by TermMan.is_sequent_term (so a sequent rebuilt from
   the view is a real sequent, not a generic Perv!sequent term).  The
   cases: equal sequents; a variable in a hypothesis, in the conclusion
   and in the args; a variable bound to a whole sequent (the view rebuilt
   by my_mk_term); a sequent nested in a term; a context hypothesis;
   different numbers of hypotheses, different args and a clash in the
   conclusion (no unifier); and a cycle through a sequent.
   The expected output is as the code printed it when the test was
   written. *)
open Lm_symbol
open Refiner.Refiner
open Term
open TermMan
open Term_sig

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let var s = mk_var_term (v s)
let c s = mk_simple_term (op s) []
let f a b = mk_simple_term (op "f") [ a; b ]
let g a = mk_simple_term (op "g") [ a ]

let seq ?(arg = c "arg") hyps concl =
  mk_sequent_term
    { sequent_args = arg; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }

let h x t = Hypothesis (v x, t)

let show t = Simple_print.SimplePrint.string_of_term t

let all_sequents_real subst =
  List.for_all
    (fun (_, t) ->
      let rec ok t =
        if is_var_term t then true
        else if is_sequent_term t then
          let s = explode_sequent t in
          ok s.sequent_args && ok s.sequent_concl
        else
          let t' = dest_term t in
          not (Opname.eq (dest_op t'.term_op).op_name Opname.sequent_opname)
          && List.for_all (fun bt -> ok (dest_bterm bt).bterm) t'.term_terms
      in
      ok t)
    subst

let case name t1 t2 consts =
  let cs = List.fold_left (fun s x -> SymbolSet.add s (v x)) SymbolSet.empty consts in
  let able = try Unify_mm.unifiable t1 t2 cs with _ -> false in
  match Unify_mm.unify t1 t2 cs with
  | subst ->
      let subst = List.sort (fun (a, _) (b, _) -> Stdlib.compare (Lm_symbol.string_of_symbol a) (Lm_symbol.string_of_symbol b)) subst in
      Printf.printf "%-34s unifiable=%b unify=OK  real-sequents=%b\n" name able (all_sequents_real subst);
      List.iter (fun (x, t) -> Printf.printf "    %s := %s\n" (Lm_symbol.string_of_symbol x) (show t)) subst
  | exception e ->
      Printf.printf "%-34s unifiable=%b unify=RAISES (%s)\n" name able
        (match e with Refiner.Refiner.RefineError.RefineError _ -> "RefineError" | _ -> Printexc.to_string e)

let () =
  let a = c "A" and b = c "B" in
  case "equal sequents" (seq [ h "x" a ] b) (seq [ h "x" a ] b) [];
  case "variable in a hypothesis" (seq [ h "x" (var "p") ] b) (seq [ h "x" a ] b) [];
  case "variable in the conclusion" (seq [ h "x" a ] (var "q")) (seq [ h "x" a ] (g b)) [];
  case "variable in the args" (seq ~arg:(var "r") [ h "x" a ] b) (seq [ h "x" a ] b) [];
  case "variables on both sides" (seq [ h "x" (var "p") ] (g b)) (seq [ h "x" a ] (g (var "q"))) [];
  case "a variable := a whole sequent" (f (var "s") a) (f (seq [ h "x" a; h "y" (var "p") ] (g b)) (var "t")) [];
  case "a sequent nested in a term" (g (seq [ h "x" (var "p") ] b)) (g (seq [ h "x" (f a b) ] b)) [];
  case "the bound name is free" (seq [ h "x" a ] (g (var "x"))) (seq [ h "y" a ] (g (var "y"))) [];
  case "a context hypothesis"
    (seq [ Context (v "H", [], []); h "x" (var "p") ] b)
    (seq [ Context (v "H", [], []); h "x" a ] b) [];
  case "different numbers of hypotheses" (seq [ h "x" a ] b) (seq [ h "x" a; h "y" a ] b) [];
  case "different args" (seq ~arg:(c "one") [ h "x" a ] b) (seq ~arg:(c "two") [ h "x" a ] b) [];
  case "a clash in the conclusion" (seq [ h "x" a ] a) (seq [ h "x" a ] b) [];
  case "a constant may not be bound" (seq [ h "x" (var "p") ] b) (seq [ h "x" a ] b) [ "p" ];
  case "a cycle through a sequent" (var "s") (g (seq [ h "x" (var "s") ] b)) [];
  case "a sequent against an operator" (seq [ h "x" a ] b) (g a) []
