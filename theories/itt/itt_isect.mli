(*
 * Intersection type.
 *
 *)

include Tactic_type

include Itt_equal
include Itt_set
include Itt_rfun

open Term

open Tactic_type

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "isect"{'A; x. 'B['x]}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext isect x: A. B[x]
 * by intersectionFormation x A
 * H >- A = A in Ui
 * H, x: A >- Ui ext B[x]
 *)
axiom intersectionFormation 'H 'x 'A :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   sequent ['ext] { 'H; x: 'A >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- isect x1:A1. B1[x1] = isect x2:A2. B2[x2] in Ui
 * by intersectionEquality y
 * H >- A1 = A2 in Ui
 * H, y: A1 >- B1[y] = B2[y] in Ui
 *)
axiom intersectionEquality 'H 'y :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[@i:l] } -->
   sequent ['ext] { 'H >- isect x1: 'A1. 'B1['x1] = isect x2: 'A2. 'B2['x2] in univ[@i:l] }

(*
 * H >- isect x: A. B[x] ext b[it]
 * by intersectionMemberFormation z
 * H >- A = A in type
 * H, z: hide(A) >- B[z] ext b[z]
 *)
axiom intersectionMemberFormation 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H; z: hide('A) >- 'B['z] } -->
   sequent ['ext] { 'H >- isect x: 'A. 'B['x] }

(*
 * H >- b1 = b2 in isect x:A. B[x]
 * by intersectionMemberEquality z
 * H >- A = A in type
 * H, z: A >- b1 = b2 in B[z]
 *)
axiom intersectionMemberEquality 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; z: 'A >- 'b1 = 'b2 in 'B['z] } -->
   sequent ['ext] { 'H >- 'b1 = 'b2 in isect x: 'A. 'B['x] }

(*
 * H >- b1 = b2 in B[a]
 * by intersectionMemberCaseEquality (isect x:A. B[x]) a
 * H >- b1 = b2 in isect x:A. B[x]
 * H >- a = a in A
 *)
axiom intersectionMemberCaseEquality 'H (isect x: 'A. 'B['x]) 'a :
   sequent [squash] { 'H >- 'b1 = 'b2 in isect x: 'A. 'B['x] } -->
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'b1 = 'b2 in 'B['a] }

(*
 * H, x: isect y: A. B[y], J[x] >- T[x]
 * by intersectionElimination a z v
 * H, x: isect y: A. B[y], J[x] >- a = a in A
 * H, x: isect y: A. B[y], J[x], z: B[a], v: z = f in B[a] >- T[x]
 *)
axiom intersectionElimination 'H 'J 'a 'x 'y 'v :
   sequent [squash] { 'H; x: isect y: 'A. 'B['y]; 'J['x] >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H; x: isect y: 'A. 'B['y]; 'J['x]; z: 'B['a]; v: 'z = 'x in 'B['a] >- 'T['x] } -->
   sequent ['ext] { 'H; x: isect y: 'A. 'B['y]; 'J['x] >- 'T['x] }

(*
 * H >- isect a1:A1. B1 <= isect a2:A2. B2
 * by intersectionSubtype
 *
 * H >- A2 <= A1
 * H, a: A1 >- B1[a] <= B2[a]
 *)
axiom intersectionSubtype 'H 'a :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { 'H >- subtype{ (isect a1:'A1. 'B1['a1]); (isect a2:'A2. 'B2['a2]) } }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_isectT : int -> tactic
val eqcd_isectT : tactic

val is_isect_term : term -> bool
val dest_isect : term -> string * term * term
val mk_isect_term : string -> term -> term -> term

(*
 * $Log$
 * Revision 1.3  1998/04/22 22:44:52  jyh
 * *** empty log message ***
 *
 * Revision 1.2  1997/08/06 16:18:33  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:15  jyh
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
 * Revision 1.4  1996/09/02 19:37:27  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.3  1996/05/21 02:16:53  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:03  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/30 01:37:14  jyh
 * Initial version of ITT.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
