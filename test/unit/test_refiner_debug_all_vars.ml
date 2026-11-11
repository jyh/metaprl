(* Refiner_debug (TERMS = both) runs TermMan.all_vars in std and ds and
   compared the two sets.  all_vars includes BOUND names, and after a
   capture-avoiding substitution std and ds may name a renamed binder
   differently (subst (lam x. pair{x; y}) [y := x; z := x1] binds x2 in
   std and x1 in ds), so the sets of two alpha-equal terms differ and the
   checker reported it (itt_vec_sequent_term under the census).  Callers
   use all_vars to choose names that clash with nothing in the term, so
   any set containing both sides' names serves both.

   For each case this test prints the set all_vars (and all_vars_terms on
   a one-element list) returns, or the report.  The expected output is as
   the code printed it when the test was written. *)
module D = Refiner_debug.MakeRefinerDebug (Refiner_std.Refiner) (Refiner_ds.Refiner)
open D

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let var s = Term.mk_var_term (v s)
let a = Term.mk_simple_term (op "A") []
let pair x y = Term.mk_simple_term (op "pair") [ x; y ]
let lam x body = TermOp.mk_dep0_dep1_term (op "lam") (v x) a body
let show s = "{" ^ String.concat ", " (List.map Lm_symbol.string_of_symbol (Lm_symbol.SymbolSet.elements s)) ^ "}"

let report name f =
  match f () with
  | s -> Printf.printf "%-44s %s\n" name s
  | exception Invalid_argument m -> Printf.printf "%-44s REPORT %s\n" name m
  | exception e -> Printf.printf "%-44s RAISES %s\n" name (Printexc.to_string e)

let case name t =
  report (name ^ ": all_vars") (fun () -> show (TermMan.all_vars t));
  report (name ^ ": all_vars_terms") (fun () -> show (TermMan.all_vars_terms [ t ]));
  report (name ^ ": free_vars_set") (fun () -> show (TermSubst.free_vars_set t))

let () =
  case "no renaming" (lam "x" (pair (var "x") (var "y")));
  case "renamed alike" (TermSubst.subst1 (lam "x" (pair (var "x") (var "y"))) (v "y") (var "x"));
  case "[y := x; z := x1]" (TermSubst.subst (lam "x" (pair (var "x") (var "y"))) [ v "y"; v "z" ] [ var "x"; var "x1" ]);
  case "[y := x; z := x1; w := x2]"
    (TermSubst.subst (lam "x" (pair (var "x") (var "y"))) [ v "y"; v "z"; v "w" ] [ var "x"; var "x1"; var "x2" ])
