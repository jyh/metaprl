(*
 * Quotient type.
 *
 *)

include Tactic_type

include Itt_equal
include Itt_set
include Itt_rfun

open Refiner.Refiner.Term

open Tactic_type

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "quot"{'A; x, y. 'E['x; 'y]}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext quot x, y: A // E
 * by quotientFormation (quot x, y: A // E) z u v
 *
 * H >- A = A in Ui
 * H, x: A, y: A >- E[x, y] = E[x, y] in Ui
 * H, x: A >- E[x, x]
 * H, x: A, y: A, u: E[x, y] >- E[y, x]
 * H, x: A, y: A, z: A, u: E[x, y], v: E[y, z] >- E[x, z]
 *)
axiom quotientFormation 'H (quot x, y: 'A // 'E['x; 'y]) 'z 'u 'v :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A; y: 'A >- 'E['x; 'y] = 'E['x; 'y] in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A >- 'E['x; 'x] } -->
   sequent [squash] { 'H; x: 'A; y: 'A; u: 'E['x; 'y] >- 'E['y; 'x] } -->
   sequent [squash] { 'H; x: 'A; y: 'A; z: 'A; u: 'E['x; 'y]; v: 'E['y; 'z] >- 'E['x; 'z] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- quot x1, y1: A1 // E1 = quot x2, y2. A2 // E2 in Ui
 * by quotientWeakEquality x y z u v
 *
 * H >- A1 = A2 in Ui
 * H, x: A1, y: A1 >- E1[x, y] = E2[x, y] in Ui
 * H, x: A1 >- E1[x, x]
 * H, x: A1, y: A1, u: E1[x, y] >- E1[y, x]
 * H, x: A1, y: A1, z: A1, u: E1[x, y], v: E1[y, z] >- E1[x, z]
 *)
axiom quotientWeakEquality 'H 'x 'y 'z 'u 'v :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A1; y: 'A1 >- 'E1['x; 'y] = 'E2['x; 'y] in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A1 >- 'E1['x; 'x] } -->
   sequent [squash] { 'H; x: 'A1; y: 'A1; u: 'E1['x; 'y] >- 'E1['y; 'x] } -->
   sequent [squash] { 'H; x: 'A1; y: 'A1; z: 'A1; u: 'E1['x; 'y]; v: 'E1['y; 'z] >- 'E1['x; 'z] } -->
   sequent ['ext] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1]
                   = quot x2, y2: 'A2 // 'E2['x2; 'y2]
                   in univ[@i:l]
           }

(*
 * H >- quot x1, y1: A1 // E1 = quot x2, y2. A2 // E2 in Ui
 * by quotientEquality r s v
 *
 * H >- quot x1, y1: A1 // E1 = quot x1, y1: A1 // E1 in Ui
 * H >- quot x2, y2. A2 // E2 = quot x2, y2. A2 // E2 in Ui
 * H >- A1 = A2 in Ui
 * H; v: A1 = A2 in Ui; r: A1; s: A1 >- E1[r, s] -> E2[r, s]
 * H; v: A1 = A2 in Ui; r: A1; s: A1 >- E2[r, s] -> E1[r, s]
 *)
axiom quotientEquality 'H 'r 's 'v :
   sequent [squash] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1] = quot x1, y1: 'A1 // 'E1['x1; 'y1] in univ[@i:l] } -->
   sequent [squash] { 'H >- quot x2, y2: 'A2 // 'E2['x2; 'y2] = quot x2, y2: 'A2 // 'E2['x2; 'y2] in univ[@i:l] } -->
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; v: 'A1 = 'A2 in univ[@i:l]; r: 'A1; s: 'A1 >- 'E1['r; 's] -> 'E2['r; 's] } -->
   sequent [squash] { 'H; v: 'A1 = 'A2 in univ[@i:l]; r: 'A1; s: 'A1 >- 'E2['r; 's] -> 'E1['r; 's] } -->
   sequent ['ext] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1] = quot x2, y2: 'A2 // 'E2['x2; 'y2] in univ[@i:l] }

(*
 * H >- quot x, y: A // E ext a
 * by quotient_memberFormation
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- A ext a
 *)
axiom quotient_memberFormation 'H :
   sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   sequent ['ext] { 'H >- 'A } -->
   sequent ['ext] { 'H >- quot x, y: 'A // 'E['x; 'y] }

(*
 * H >- a1 = a2 in quot x, y: A // E
 * by quotient_memberWeakEquality
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- x1 = a2 in A
 *)
axiom quotient_memberWeakEquality 'H :
   sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] }

(*
 * H >- a1 = a2 in quot x, y: A // E
 * by quotient_memberEquality
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- a1 = a1 in A
 * H >- a2 = a2 in A
 * H >- E[a1; a2]
 *)
axiom quotient_memberEquality 'H :
   sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   sequent [squash] { 'H >- 'a1 = 'a1 in 'A } -->
   sequent [squash] { 'H >- 'a2 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'E['a1; 'a2] } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] }

(*
 * !!!!CHECK!!!!
 *
 * H, a: quot x, y: A // E, J[x] >- s[a] = t[a] in T[a]
 * by quotientElimination v w z
 *
 * H, a: quot x, y: A // E, J[x] >- T[a] = T[a] in Ui
 * H, a: quot x, y: A // E, J[x], v: A, w: A, z: E[v, w] >- s[v] = t[w] in T[v]
 *)
axiom quotientElimination 'H 'J 'v 'w 'z :
   sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- "type"{'T['a]} } -->
   sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a];
             v: 'A; w: 'A; z: 'E['v; 'w] >- 's['v] = 't['w] in 'T['v]
           } -->
   sequent ['ext] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- 's['a] = 't['a] in 'T['a] }

(*
 * !!!!CHECK!!!!
 *
 * H, x: a1 = a2 in quot x, y: A // E, J[x] >- T[x]
 * by quotient_equalityElimination v
 *
 * H, x: a1 = a2 in quot x, y: A // E, J[x], v: hide(E[a, b]) >- T[x]
 *)
axiom quotient_equalityElimination 'H 'J 'v :
   sequent ['ext] { 'H; x: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; 'J['x]; v: hide('E['a1; 'a2]) >- 'T['x] } -->
   sequent ['ext] { 'H; x: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; 'J['x] >- 'T['x] }

(*
 * H >- quot x1, y1: A1 // E1[x1; y1] <= quot x2, y2: A2 // E2[x2; y2]
 * by quotientSubtype
 *
 * H >- A1 <= A2
 * H, x1: A1, y1: A1 >- E1[x1; y1] => E2[x2; y2]
 * H >- quot x1, y1: A1 // E1[x1; y1] in type
 * H >- quot x2, y2: A2 // E2[x2; y2] in type
 *)
axiom quotientSubtype 'H 'a1 'a2 :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H; a1: 'A1; a2: 'A1 (* ; 'E1['a1; 'a2] *) >- 'E2['a1; 'a2] } -->
   sequent [squash] { 'H >- "type"{(quot x1, y1: 'A1 // 'E1['x1; 'y1])} } -->
   sequent [squash] { 'H >- "type"{(quot x2, y2: 'A2 // 'E2['x2; 'y2])} } -->
   sequent ['ext] { 'H >- subtype{ (quot x1, y1: 'A1 // 'E1['x1; 'y1]); (quot x2, y2: 'A2 // 'E2['x2; 'y2]) } };;

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_quotientT : int -> tactic
val eqcd_quotientT : tactic

val is_quotient_term : term -> bool
val dest_quotient : term -> string * string * term * term
val mk_quotient_term : string -> string -> term -> term -> term

(*
 * $Log$
 * Revision 1.5  1998/06/01 13:56:10  jyh
 * Proving twice one is two.
 *
 * Revision 1.4  1998/05/28 13:47:55  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.3  1998/04/22 22:45:04  jyh
 * *** empty log message ***
 *
 * Revision 1.2  1997/08/06 16:18:38  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:23  jyh
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
 * Revision 1.4  1996/09/02 19:37:37  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.3  1996/05/21 02:17:04  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:11  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/30 01:37:17  jyh
 * Initial version of ITT.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
