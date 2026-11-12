(* The term_ds implementation's small arms (refiner/term_ds) that the
   proof census runs and no unit test did (2026-11-12 census, 8 lines in
   term_op_ds, term_base_ds and term_subst_ds): is_no_subterms_term on
   another operator, a term with subterms and a variable; one_subterm's
   arity refusal; is_some_var_free with no variables; a delayed
   substitution pushed into a bound term whose binder shadows a
   substituted variable (dropped there, the others kept, a captured
   binder renamed); alpha_equal over two binders with an inner binder of
   the same name.  The expected file is the output of the code as
   written (2026-11-12), never typed.
   Not reached, declared: eq_filt_vars's middle branch (term_subst_ds).
   A mutant that stops remove_var removing a later pair survives: these
   alpha_equal cases do not distinguish it. *)
open Refiner.Refiner
open TermType
open Term
open TermOp
open TermSubst
open RefineError

let op s = Opname.make_opname [ s; "Tds" ]
let v = Lm_symbol.add
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o []
let var x = mk_var_term (v x)
let bnd o xs t = mk_term (mk_op (op o) []) [ mk_bterm (List.map v xs) t ]
let sp = Simple_print.SimplePrint.string_of_term
let run name f =
  let r = try f () with RefineError (s, _) -> "REFUSED: " ^ s | Failure s -> "FAILURE: " ^ s in
  Printf.printf "%-52s %s\n" name r
let b x = string_of_bool x
let ae0 n t1 t2 = run n (fun () -> b (alpha_equal t1 t2))

let () =
  print_endline "== is_no_subterms_term / one_subterm";
  run "a, is a" (fun () -> b (is_no_subterms_term (op "a") (c0 "a")));
  run "b, is a" (fun () -> b (is_no_subterms_term (op "a") (c0 "b")));
  run "a{c}, is a" (fun () -> b (is_no_subterms_term (op "a") (app "a" [ c0 "c" ])));
  run "x, is a" (fun () -> b (is_no_subterms_term (op "a") (var "x")));
  run "one_subterm f{c}" (fun () -> sp (one_subterm (app "f" [ c0 "c" ])));
  run "one_subterm c" (fun () -> sp (one_subterm (c0 "c")));
  run "one_subterm f{c; d}" (fun () -> sp (one_subterm (app "f" [ c0 "c"; c0 "d" ])));
  print_endline "== is_some_var_free";
  run "[] in f{x}" (fun () -> b (is_some_var_free [] (app "f" [ var "x" ])));
  run "[x] in f{x}" (fun () -> b (is_some_var_free [ v "x" ] (app "f" [ var "x" ])));
  run "[y] in f{x}" (fun () -> b (is_some_var_free [ v "y" ] (app "f" [ var "x" ])));
  print_endline "== subst under a binder that shadows it";
  let t = app "pair" [ var "x"; bnd "lam" [ "x" ] (app "f" [ var "x" ]) ] in
  run "pair{x; lam{x. f{x}}} [x := a]" (fun () -> sp (subst t [ v "x" ] [ c0 "a" ]));
  let t2 = app "pair" [ app "g" [ var "x"; var "y" ]; bnd "lam" [ "x" ] (app "f" [ var "x"; var "y" ]) ] in
  run "pair{g{x;y}; lam{x. f{x;y}}} [x := a; y := b]" (fun () -> sp (subst t2 [ v "x"; v "y" ] [ c0 "a"; c0 "b" ]));
  run "the same, [y := b; x := a]" (fun () -> sp (subst t2 [ v "y"; v "x" ] [ c0 "b"; c0 "a" ]));
  let t3 = app "pair" [ app "g" [ var "x"; var "y"; var "z" ]; bnd "lam" [ "x"; "y" ] (app "f" [ var "x"; var "y"; var "z" ]) ] in
  run "lam{x,y. f{x;y;z}} with x, y, z := a, b, c" (fun () -> sp (subst t3 [ v "x"; v "y"; v "z" ] [ c0 "a"; c0 "b"; c0 "c" ]));
  let pb xs body = mk_term (mk_op (op "pair") []) [ mk_bterm [] (var "x"); mk_bterm (List.map v xs) body ] in
  run "pair{x; x. f{x}} [x := a] (x shadowed)" (fun () -> sp (subst (pb [ "x" ] (app "f" [ var "x" ])) [ v "x" ] [ c0 "a" ]));
  run "pair{x; x. f{x; y}} [x := a; y := b]" (fun () ->
      sp (subst (pb [ "x" ] (app "f" [ var "x"; var "y" ])) [ v "x"; v "y" ] [ c0 "a"; c0 "b" ]));
  run "pair{x; y. f{x; y}} [x := a; y := b]" (fun () ->
      sp (subst (pb [ "y" ] (app "f" [ var "x"; var "y" ])) [ v "x"; v "y" ] [ c0 "a"; c0 "b" ]));
  run "pair{x; y. f{x; y}} [x := y] (y captured, renamed)" (fun () ->
      sp (subst (pb [ "y" ] (app "f" [ var "x"; var "y" ])) [ v "x" ] [ var "y" ]));
  print_endline "== alpha_equal with an inner binder of the same name";
  ae0 "lam2{x,y. f{x;y}} = lam2{a,b. f{a;b}}" (bnd "lam2" [ "x"; "y" ] (app "f" [ var "x"; var "y" ])) (bnd "lam2" [ "a"; "b" ] (app "f" [ var "a"; var "b" ]));
  ae0 "lam2{x,y. f{x;y}} = lam2{a,b. f{b;a}}" (bnd "lam2" [ "x"; "y" ] (app "f" [ var "x"; var "y" ])) (bnd "lam2" [ "a"; "b" ] (app "f" [ var "b"; var "a" ]));
  let l2 x y body = bnd "lam2" [ x; y ] body in
  let ae n t1 t2 = run n (fun () -> b (alpha_equal t1 t2)) in
  ae "lam2{x,y. lam{x. f{x;y}}} = lam2{a,b. lam{x. f{x;b}}}"
    (l2 "x" "y" (bnd "lam" [ "x" ] (app "f" [ var "x"; var "y" ])))
    (l2 "a" "b" (bnd "lam" [ "x" ] (app "f" [ var "x"; var "b" ])));
  ae "lam2{x,y. lam{x. f{x;y}}} = lam2{a,b. lam{x. f{x;a}}}"
    (l2 "x" "y" (bnd "lam" [ "x" ] (app "f" [ var "x"; var "y" ])))
    (l2 "a" "b" (bnd "lam" [ "x" ] (app "f" [ var "x"; var "a" ])));
  ae "lam2{x,y. lam{y. f{x;y}}} = lam2{a,b. lam{y. f{a;y}}}"
    (l2 "x" "y" (bnd "lam" [ "y" ] (app "f" [ var "x"; var "y" ])))
    (l2 "a" "b" (bnd "lam" [ "y" ] (app "f" [ var "a"; var "y" ])));
  ae "lam2{x,y. lam{x. g{x}}} = lam2{a,b. lam{x. g{x}}}"
    (l2 "x" "y" (bnd "lam" [ "x" ] (app "g" [ var "x" ])))
    (l2 "a" "b" (bnd "lam" [ "x" ] (app "g" [ var "x" ])));
  ae "lam2{x,y. pair{lam{x. g{x}}; y}} = lam2{a,b. pair{lam{x. g{x}}; b}}"
    (l2 "x" "y" (app "pair" [ bnd "lam" [ "x" ] (app "g" [ var "x" ]); var "y" ]))
    (l2 "a" "b" (app "pair" [ bnd "lam" [ "x" ] (app "g" [ var "x" ]); var "b" ]));
  ae "lam2{x,y. lam{x. f{x;y;z}}} = lam2{x,b. lam{x. f{x;b;z}}}"
    (l2 "x" "y" (bnd "lam" [ "x" ] (app "f" [ var "x"; var "y"; var "z" ])))
    (l2 "x" "b" (bnd "lam" [ "x" ] (app "f" [ var "x"; var "b"; var "z" ])))
