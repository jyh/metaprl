(*
 * Set type.
 *
 *)

open Term

include Itt_equal
include Itt_subtype
include Itt_unit
include Itt_struct

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare set{'A; x. 'B['x]}
declare hide{'A}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext { a:A | B }
 * by setFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
axiom setFormation 'H 'a 'A :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   sequent ['ext] { 'H; a: 'A >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- { a1:A1 | B1[a1] } = { a2:A2 | B2[a2] } in Ui
 * by setEquality x
 *
 * H >- A1 = A2 in Ui
 * H, x: A1 >- B1[x] = B2[x] in Ui
 *)
axiom setEquality 'H 'x :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[@i:l] } -->
   sequent ['ext] { 'H >- { a1:'A1 | 'B1['a1] } = { a2:'A2 | 'B2['a2] } in univ[@i:l] }

(*
 * H >- { a:A | B[a] } ext a
 * by setMemberFormation Ui a z
 *
 * H >- a = a in A
 * H >- B[a]
 * H, z: A >- B[z] = B[z] in Ui
 *)
axiom setMemberFormation 'H 'a 'z :
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext]   { 'H >- 'B['a] } -->
   sequent [squash] { 'H; z: 'A >- "type"{'B['z]} } -->
   sequent ['ext]   { 'H >- { x:'A | 'B['x] } }

(*
 * H >- a1 = a2 in { a:A | B }
 * by setMemberEquality Ui x
 *
 * H >- a1 = a2 in A
 * H >- B[a1]
 * H, x: A >- B[x] = B[x] in Ui
 *)
axiom setMemberEquality 'H 'x :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'B['a1] } -->
   sequent [squash] { 'H; x: 'A >- "type"{'B['x]} } -->
   sequent ['ext]   { 'H >- 'a1 = 'a2 in { a:'A | 'B['a] } }

(*
 * H, u: { x:A | B }, J[u] >- T[u] ext t[y]
 * by setElimination y v
 *
 * H, u: { x:A | B }, y: A; v: hide{B[y]}; J[y] >- T[y]
 *)
axiom setElimination 'H 'J 'u 'y 'v :
   sequent [squash] { 'H; u: { x:'A | 'B['x] }; y: 'A; v: 'B['y]; 'J['y] >- 'T['y] } -->
   sequent [squash] { 'H; u: { x:'A | 'B['x] }; 'J['u] >- 'T['u] }

(*
 * H, u: { x:A | B }, J[u] >> T[u] ext t[y]
 * by setElimination2 y v z
 * H, u: { x:A | B }, y: A; v: hide(B[y]); J[y] >> T[y]
 *)
axiom setElimination2 'H 'J 'u 'y 'v :
   sequent [it; 'prop] { 'H; u: { x:'A | 'B['x] }; y: 'A; v: hide{'B['y]}; 'J['y] >- 'T['y] } -->
   sequent [it; 'prop] { 'H; u: { x:'A | 'B['x] }; 'J['u] >- 'T['u] }

(*
 * Unhiding.
 *)
axiom hideElimination 'H 'J :
   sequent [squash] { 'H; u: 'P; 'J[it] >- 'T[it] } -->
   sequent [squash] { 'H; u: hide{'P}; 'J['u] >- 'T['u] }

(*
 * Subtyping.
 *)
axiom set_subtype 'H :
   sequent [squash] { 'H >- "type"{ { a: 'A | 'B['a] } } } -->
   sequent ['ext] { 'H >- subtype{ { a: 'A | 'B['a] }; 'A } }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_setT : int -> tactic
val eqcd_setT : tactic

(* Hiding and unhiding *)
val squashT : tactic
val unhideT : int -> tactic
val unhideAllT : tactic

(* Primitives *)
val is_set_term : term -> bool
val dest_set : term -> string * term * term
val mk_set_term : string -> term -> term -> term

val is_hide_term : term -> bool
val dest_hide : term -> term
val mk_hide_term : term -> term

(*
 * $Log$
 * Revision 1.3  1998/04/09 18:26:09  jyh
 * Working compiler once again.
 *
 * Revision 1.2  1997/08/06 16:18:41  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:25  jyh
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
 * Revision 1.4  1996/09/02 19:37:39  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.3  1996/05/21 02:17:10  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:14  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/30 01:37:18  jyh
 * Initial version of ITT.
 *
 * Revision 1.2  1996/03/28 02:51:28  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.1  1996/03/05 19:59:41  jyh
 * Version just before LogicalFramework.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
