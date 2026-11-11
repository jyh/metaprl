(* TermAddr.term_subterm returns the subterm at an address, from under the
   binders the address crosses, without them.  The debug refiner (TERMS =
   both) paired std's subterm with ds's as they came, but after a
   capture-avoiding substitution the two may name a renamed binder
   differently (x2 in std, x1 in ds for subst (lam x. pair{x; y})
   [y := x; z := x1]), so the subterm's halves named the same variable
   differently; in itt_list2 the rewriter then reported "i1" vs "i".

   For each case this test takes a subterm by address in the debug
   refiner and prints its free variables (the debug refiner reports if the
   halves disagree).  The expected output is as the code printed it when
   the test was written. *)
module D = Refiner_debug.MakeRefinerDebug (Refiner_std.Refiner) (Refiner_ds.Refiner)
open D

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let var s = Term.mk_var_term (v s)
let a = Term.mk_simple_term (op "A") []
let pair x y = Term.mk_simple_term (op "pair") [ x; y ]
let lam x body = TermOp.mk_dep0_dep1_term (op "lam") (v x) a body
let show s = "{" ^ String.concat ", " (List.map Lm_symbol.string_of_symbol (Lm_symbol.SymbolSet.elements s)) ^ "}"

let case name t path =
  let addr = TermAddr.make_address (List.map (fun i -> Term_addr_sig.Subterm i) path) in
  let p = "[" ^ String.concat ";" (List.map string_of_int path) ^ "]" in
  match TermAddr.term_subterm t addr with
  | s -> (
      match TermSubst.free_vars_set s with
      | fv -> Printf.printf "%-34s at %-6s free vars %s\n" name p (show fv)
      | exception Invalid_argument m -> Printf.printf "%-34s at %-6s REPORT %s\n" name p m)
  | exception Invalid_argument m -> Printf.printf "%-34s at %-6s REPORT %s\n" name p m

let () =
  let r1 = TermSubst.subst (lam "x" (pair (var "x") (var "y"))) [ v "y"; v "z" ] [ var "x"; var "x1" ] in
  let r2 = TermSubst.subst (lam "x" (pair (var "x") (var "y"))) [ v "y"; v "z"; v "w" ] [ var "x"; var "x1"; var "x2" ] in
  let nested = TermSubst.subst (lam "x" (lam "y" (pair (var "x") (pair (var "y") (var "u")))))
      [ v "u"; v "z" ] [ pair (var "x") (var "y"); pair (var "x1") (var "y1") ] in
  case "no renaming" (lam "x" (pair (var "x") (var "y"))) [ 2 ];
  case "[y := x; z := x1], the body" r1 [ 2 ];
  case "[y := x; z := x1], inside the body" r1 [ 2; 1 ];
  case "[y := x; z := x1; w := x2]" r2 [ 2 ];
  case "two binders renamed" nested [ 2; 2 ];
  case "the argument (no binder crossed)" r1 [ 1 ]
