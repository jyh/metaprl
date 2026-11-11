(* Refiner_debug (TERMS = both) runs every term operation in both term
   implementations, std and ds, and reports any difference.  A
   capture-avoiding substitution may rename a binder, and the two
   implementations choose the fresh name differently: with
   subst (lam x. pair{x; y}) [y := x; z := x1] std avoids every free
   variable of the substitution's range and names the binder x2, while ds
   avoids those of the substituted variables that occur and names it x1.
   Both are correct (the terms are alpha-equal), but TermOp.dest_* compared
   the two names and reported a mismatch, and the census under TERMS =
   both lost proof statuses on it (itt_nat, itt_list2, ...).

   This test builds such terms in the debug refiner and, for each case,
   prints the binder dest_dep0_dep1_term (or dest_dep0_dep0_dep3_term)
   returns, and whether rebuilding the term from the returned parts gives
   a term alpha-equal to the one taken apart (the returned binder must be
   the one each side's body uses).  The expected output is as the code
   printed it when the test was written. *)
module D = Refiner_debug.MakeRefinerDebug (Refiner_std.Refiner) (Refiner_ds.Refiner)
open D

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let var s = Term.mk_var_term (v s)
let a = Term.mk_simple_term (op "A") []
let pair x y = Term.mk_simple_term (op "pair") [ x; y ]
let lam x body = TermOp.mk_dep0_dep1_term (op "lam") (v x) a body
let names l = String.concat "," (List.map Lm_symbol.string_of_symbol l)

let report name f =
  match f () with
  | s -> Printf.printf "%-46s %s\n" name s
  | exception Invalid_argument m -> Printf.printf "%-46s REPORT %s\n" name m
  | exception e -> Printf.printf "%-46s RAISES %s\n" name (Printexc.to_string e)

let dest1 name t =
  report name (fun () ->
      let b, t1, t2 = TermOp.dest_dep0_dep1_term (op "lam") t in
      let back = TermOp.mk_dep0_dep1_term (op "lam") b t1 t2 in
      Printf.sprintf "%s rebuilt-alpha-equal=%b" (names [ b ]) (TermSubst.alpha_equal back t))

let tri x y z body = TermOp.mk_dep0_dep0_dep3_term (op "tri") a a (v x) (v y) (v z) body

let dest3 name t =
  report name (fun () ->
      let t0, t1, b1, b2, b3, t2 = TermOp.dest_dep0_dep0_dep3_term (op "tri") t in
      let back = TermOp.mk_dep0_dep0_dep3_term (op "tri") t0 t1 b1 b2 b3 t2 in
      Printf.sprintf "%s rebuilt-alpha-equal=%b" (names [ b1; b2; b3 ]) (TermSubst.alpha_equal back t))

let () =
  dest1 "no renaming" (lam "x" (pair (var "x") (var "y")));
  dest1 "one substitution renames x to x1" (TermSubst.subst1 (lam "x" (pair (var "x") (var "y"))) (v "y") (var "x"));
  dest1 "a range variable that does not occur" (TermSubst.subst1 (lam "x" (pair (var "x") (var "z"))) (v "y") (var "x"));
  dest1 "[y := x; z := x1], z absent"
    (TermSubst.subst (lam "x" (pair (var "x") (var "y"))) [ v "y"; v "z" ] [ var "x"; var "x1" ]);
  dest1 "[y := x; z := x1; w := x2], z w absent"
    (TermSubst.subst (lam "x" (pair (var "x") (var "y"))) [ v "y"; v "z"; v "w" ] [ var "x"; var "x1"; var "x2" ]);
  dest1 "the renamed body still sees a free x1"
    (TermSubst.subst (lam "x" (pair (var "x") (pair (var "y") (var "x1")))) [ v "y"; v "z" ] [ var "x"; var "x2" ]);
  dest3 "three binders, none renamed" (tri "x" "y" "z" (pair (var "x") (pair (var "y") (var "z"))));
  dest3 "three binders, [u := x; w := x1], w absent"
    (TermSubst.subst (tri "x" "y" "z" (pair (var "x") (pair (var "u") (var "z")))) [ v "u"; v "w" ] [ var "x"; var "x1" ])
