(* Unify_mm (refiner/reflib) with second-order variables, mixed function
   symbols and constants: the branches the proof census runs and neither
   test_unify_mm (f, g, c, lam) nor test_unify_mm_sequent reaches
   (2026-11-11 reach census, 9 lines).  Unify_mm treats a second-order
   variable 'a<conts>[args] as a function symbol named by the variable and
   its contexts, applied to its arguments; so two of them unify argument by
   argument when name and contexts agree, and clash otherwise, as does a
   second-order variable against an ordinary operator, or one operator at
   two arities.  Each case prints unifiable, the substitution unify returns
   (sorted) or the exception it raises, and, for a substitution s, whether
   s(t1) and s(t2) are alpha-equal (it is a unifier), "<- DIFFERS" when
   unifiable and unify disagree or s is not a unifier.  The constants (the
   SymbolSet argument) are variables that may not be bound. *)
open Lm_symbol
open Refiner.Refiner
open Term
open TermType
open TermMan

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let var s = mk_var_term (v s)
let c s = mk_simple_term (op s) []
let app o ts = mk_simple_term (op o) ts
let so name conts args = mk_so_var_term (v name) (List.map v conts) args
let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
let sp = Simple_print.SimplePrint.string_of_term

let subst s t = TermSubst.subst t (List.map fst s) (List.map snd s)
let case name ?(consts = []) t1 t2 =
  let cs = SymbolSet.of_list (List.map v consts) in
  let u = try string_of_bool (Unify_mm.unifiable t1 t2 cs) with e -> "raises " ^ Printexc.to_string e in
  let r, ok =
    try
      let s = Unify_mm.unify t1 t2 cs in
      let s = List.sort (fun (a, _) (b, _) -> Stdlib.compare (Lm_symbol.to_string a) (Lm_symbol.to_string b)) s in
      let unif = TermSubst.alpha_equal (subst s t1) (subst s t2) in
      "{" ^ String.concat ", " (List.map (fun (x, t) -> Lm_symbol.to_string x ^ " := " ^ sp t) s) ^ "}"
      ^ (if unif then " unifier" else " NOT A UNIFIER"), unif && u = "true"
    with
    | RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")", u = "false"
    | e -> "raises " ^ Printexc.to_string e, u = "false"
  in
  Printf.printf "%-46s unifiable %-5s unify %s%s\n" name u r (if ok then "" else "  <- DIFFERS")

let () =
  case "'a['x] =? 'a['y]" (so "a" [] [ var "x" ]) (so "a" [] [ var "y" ]);
  case "'a['x; c] =? 'a[g{'y}; 'z]" (so "a" [] [ var "x"; c "c" ]) (so "a" [] [ app "g" [ var "y" ]; var "z" ]);
  case "'a['x] =? 'b['x]" (so "a" [] [ var "x" ]) (so "b" [] [ var "x" ]);
  case "'a<H>[c] =? 'a<J>[c]" (so "a" [ "H" ] [ c "c" ]) (so "a" [ "J" ] [ c "c" ]);
  case "'a<H>[c] =? 'a<H>[c]" (so "a" [ "H" ] [ c "c" ]) (so "a" [ "H" ] [ c "c" ]);
  case "'a['x] =? 'a['x; 'y] (arities)" (so "a" [] [ var "x" ]) (so "a" [] [ var "x"; var "y" ]);
  case "f{'a[c]} =? f{g{c}}" (app "f" [ so "a" [] [ c "c" ] ]) (app "f" [ app "g" [ c "c" ] ]);
  case "f{g{c}} =? f{'a[c]}" (app "f" [ app "g" [ c "c" ] ]) (app "f" [ so "a" [] [ c "c" ] ]);
  case "f{'x} =? f{'a['y]}" (app "f" [ var "x" ]) (app "f" [ so "a" [] [ var "y" ] ]);
  case "f{'x} =? f{'a<H>['y]}" (app "f" [ var "x" ]) (app "f" [ so "a" [ "H" ] [ var "y" ] ]);
  case "'x =? 'a['x] (cycle)" (var "x") (so "a" [] [ var "x" ]);
  case "f{c} =? f{c; c} (arities)" (app "f" [ c "c" ]) (app "f" [ c "c"; c "c" ]);
  case "h{f{'x}; f{c; 'y}} =? h{f{c}; f{c; c}}" (app "h" [ app "f" [ var "x" ]; app "f" [ c "c"; var "y" ] ]) (app "h" [ app "f" [ c "c" ]; app "f" [ c "c"; c "c" ] ]);
  case "h{'z; 'z} =? h{f{c}; f{c; c}}" (app "h" [ var "z"; var "z" ]) (app "h" [ app "f" [ c "c" ]; app "f" [ c "c"; c "c" ] ]);
  case "lam x. f{'x; 'z} =? lam y. f{'y; c}, consts {x}" ~consts:[ "x" ] (lam "x" (app "f" [ var "x"; var "z" ])) (lam "y" (app "f" [ var "y"; c "c" ]));
  case "lam x. f{'x; 'z} =? 'w, consts {x}" ~consts:[ "x" ] (lam "x" (app "f" [ var "x"; var "z" ])) (var "w");
  case "f{lam x. 'x; 'z} =? f{'w; lam y. 'y}, consts {x; y}" ~consts:[ "x"; "y" ] (app "f" [ lam "x" (var "x"); var "z" ]) (app "f" [ var "w"; lam "y" (var "y") ]);
  case "'x =? c, consts {x}" ~consts:[ "x" ] (var "x") (c "c")
