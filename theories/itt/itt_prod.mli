(*
 * Rules for dependent product.
 *
 *)

include Tactic_type

include Itt_equal
include Itt_dprod

open Tactic_type

(*
 * H >- Ui ext A * B
 * by independentProductFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
axiom independentProductFormation 'H :
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- A1 * B1 = A2 * B2 in Ui
 * by independentProductEquality
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
axiom independentProductEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- 'A1 * 'B1 = 'A2 * 'B2 in univ[@i:l] }

(*
 * H >- A * B ext (a, b)
 * by independentPairFormation a y
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
axiom independentPairFormation 'H :
   sequent ['ext] { 'H >- 'A } -->
   sequent ['ext] { 'H >- 'B } -->
   sequent ['ext] { 'H >- 'A * 'B }

(*
 * H, A * B, J >- T ext t
 * by independentProductElimination
 * H, A * B, u: A, v: B, J >- T ext t
 *)
axiom independentProductElimination 'H 'J 'z 'u 'v :
   sequent ['ext] { 'H; z: 'A * 'B; u: 'A; v: 'B; 'J['u, 'v] >- 'T['u, 'v] } -->
   sequent ['ext] { 'H; z: 'A * 'B; 'J['z] >- 'T['z] }

(*
 * H >- (a1, b1) = (a2, b2) in A * B
 * by independentPairEquality
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B
 *)
axiom independentPairEquality 'H :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B } -->
   sequent ['ext] { 'H >- ('a1, 'b1) = ('a2, 'b2) in 'A * 'B }

(*
 * H >- A1 -> B1 <= A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H >- B1 <= B2
 *)
axiom independentProductSubtype 'H :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 * 'B1); ('A2 * 'B2) } }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_prodT : int -> tactic
val eqcd_prodT : tactic

(*
 * $Log$
 * Revision 1.4  1998/06/01 13:56:07  jyh
 * Proving twice one is two.
 *
 * Revision 1.3  1998/04/22 22:45:01  jyh
 * *** empty log message ***
 *
 * Revision 1.2  1997/08/06 16:18:37  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:21  jyh
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
 * Revision 1.5  1996/10/23 15:18:10  jyh
 * First working version of dT tactic.
 *
 * Revision 1.4  1996/09/02 19:37:35  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.3  1996/05/21 02:17:01  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:08  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/28 02:51:33  jyh
 * This is an initial version of the type theory.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
