(*
 * Rules for dependent product.
 *
 *)

open Debug
open Term
open Options
open Resource
open Refine_sig

include Var

include Itt_equal
include Itt_dprod

(* debug_string DebugLoad "Loading itt_prod..." *)

(*
 * H >- Ui ext A * B
 * by independentProductFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
prim independentProductFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[@i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   'A * 'B

(*
 * H >- A1 * B1 = A2 * B2 in Ui
 * by independentProductEquality
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
prim independentProductEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- 'A1 * 'B1 = 'A2 * 'B2 in univ[@i:l] } =
   it

(*
 * H >- A * B ext (a, b)
 * by independentPairFormation a y
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
prim independentPairFormation 'H :
   ('a : sequent ['ext] { 'H >- 'A }) -->
   ('b : sequent ['ext] { 'H >- 'B }) -->
   sequent ['ext] { 'H >- 'A * 'B } =
   'a, 'b

(*
 * H, A * B, J >- T ext t
 * by independentProductElimination 
 * H, A * B, u: A, v: B, J >- T ext t
 *)
prim independentProductElimination 'H 'J 'z 'u 'v :
   ('t : sequent ['ext] { 'H; z: 'A * 'B; u: 'A; v: 'B; 'J['u, 'v] >- 'T['u, 'v] }) -->
   sequent ['ext] { 'H; z: 'A * 'B; 'J['z] >- 'T['z] } =
   't

(*
 * H >- (a1, b1) = (a2, b2) in A * B
 * by independentPairEquality
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B
 *)
prim independentPairEquality 'H :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B } -->
   sequent ['ext] { 'H >- ('a1, 'b1) = ('a2, 'b2) in 'A * 'B } =
   it

(*
 * H >- A1 -> B1 <= A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H >- B1 <= B2
 *)
prim independentProductSubtype 'H :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 * 'B1); ('A2 * 'B2) } } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_prod p =
   let count = hyp_count p in
      independentPairFormation count p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_prod i p =
   let count = hyp_count p in
   let i' = get_pos_hyp_index i count in
   let z = var_of_hyp i' p in
      (match maybe_new_vars ["%u"; "%v"] (declared_vars p) with
          [u; v] ->
             independentProductElimination i' (count - i' - 1) z u v
        | _ ->
             failT) p

(*
 * Join them.
 *)
let d_prodT i =
   if i = 0 then
      d_concl_prod
   else
      d_hyp_prod i

let d_resource = d_resource.resource_improve d_resource (prod_term, d_prodT)

(*
 * EQCD.
 *)
let eqcd_prodT p =
   let count = hyp_count p in
      (independentProductEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (prod_term, eqcd_prodT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_prod f decl t =
   let a, b = dest_prod t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
   let le1, le2 =
      try dest_univ a', dest_univ b' with
         Term.TermMatch _ -> raise (RefineError (StringTermError ("typeinf: can't infer type for", t)))
   in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (prod_term, inf_prod)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two product types.
 *)
let prod_subtypeT p =
   (independentProductSubtype (hyp_count p)
    thenT addHiddenLabelT "subtype") p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (DSubtype ([<< 'A1 * 'B1 >>, << 'A2 * 'B2 >>;
               << 'A1 >>, << 'A2 >>;
               << 'B1 >>, << 'B2 >>],
              prod_subtypeT))

(*
 * $Log$
 * Revision 1.2  1997/08/06 16:18:36  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:20  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.3  1996/10/23 15:18:10  jyh
 * First working version of dT tactic.
 *
 * Revision 1.2  1996/05/21 02:17:00  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.1  1996/03/28 02:51:32  jyh
 * This is an initial version of the type theory.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
