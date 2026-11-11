(* Term.subterms_of_term returns the bodies of a term's bound terms without
   their binders.  The debug refiner (TERMS = both) paired std's bodies with
   ds's as they came, but after a capture-avoiding substitution the two
   implementations may name a renamed binder differently (x2 in std, x1 in
   ds for subst (lam x. pair{x; y}) [y := x; z := x1]), so a body's two
   halves used different names for the same variable.  Term_match_table
   matches on these subterms, and the rewriter's dest_var then reported
   "i1" vs "i" in itt_list2 under TERMS = both.

   For each case this test takes the subterms of a term built in the debug
   refiner and prints each subterm's free variables (the debug refiner
   reports if the two halves disagree).  The expected output is as the code
   printed it when the test was written. *)
module D = Refiner_debug.MakeRefinerDebug (Refiner_std.Refiner) (Refiner_ds.Refiner)
open D

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let var s = Term.mk_var_term (v s)
let a = Term.mk_simple_term (op "A") []
let pair x y = Term.mk_simple_term (op "pair") [ x; y ]
let lam x body = TermOp.mk_dep0_dep1_term (op "lam") (v x) a body
let show s = "{" ^ String.concat ", " (List.map Lm_symbol.string_of_symbol (Lm_symbol.SymbolSet.elements s)) ^ "}"

let case name t =
  match Term.subterms_of_term t with
  | ts ->
      List.iteri
        (fun i t ->
          let fv = try show (TermSubst.free_vars_set t) with Invalid_argument m -> "REPORT " ^ m in
          Printf.printf "%-34s subterm %d: free vars %s\n" name i fv)
        ts
  | exception Invalid_argument m -> Printf.printf "%-34s REPORT %s\n" name m

let () =
  case "no renaming" (lam "x" (pair (var "x") (var "y")));
  case "renamed alike" (TermSubst.subst1 (lam "x" (pair (var "x") (var "y"))) (v "y") (var "x"));
  case "[y := x; z := x1]" (TermSubst.subst (lam "x" (pair (var "x") (var "y"))) [ v "y"; v "z" ] [ var "x"; var "x1" ]);
  case "[y := x; z := x1; w := x2]"
    (TermSubst.subst (lam "x" (pair (var "x") (var "y"))) [ v "y"; v "z"; v "w" ] [ var "x"; var "x1"; var "x2" ])
