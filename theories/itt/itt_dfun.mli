(*
 * Dependent functions.
 *
 *)

include Itt_equal
include Itt_rfun

open Refiner.Refiner.Term

open Tacticals

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext a:A -> B
 * by functionFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
axiom functionFormation 'H 'a 'A :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   sequent ['ext] { 'H; a: 'A >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- (a1:A1 -> B1[a1]) = (a2:A2 -> B2[a2]) in Ui
 * by functionEquality x
 *
 * H >- A1 = A2 in Ui
 * H, x: A1 >- B1[x] = B2[x] in Ui
 *)
axiom functionEquality 'H 'x :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[@i:l] } -->
   sequent ['ext] { 'H >- (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[@i:l] }

(*
 * H >- a:A -> B[a] ext lambda(z. b[z])
 * by lambdaFormation Ui z
 *
 * H >- A = A in Ui
 * H, z: A >- B[z] ext b[z]
 *)
axiom lambdaFormation 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H; z: 'A >- 'B['z] } -->
   sequent ['ext] { 'H >- a:'A -> 'B['a] }

(*
 * H >- lambda(a1. b1[a1]) = lambda(a2. b2[a2]) in a:A -> B
 * by lambdaEquality Ui x
 *
 * H >- A = A in Ui
 * H, x: A >- b1[x] = b2[x] in B[x]
 *)
axiom lambdaEquality 'H 'x :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'A >- 'b1['x] = 'b2['x] in 'B['x] } -->
   sequent ['ext] { 'H >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in a:'A -> 'B['a] }

(*
 * H >- f = g in x:A -> B
 * by functionExtensionality Ui (y:C -> D) (z:E -> F) u
 *
 * H, u:A >- f(u) = g(u) in B[u]
 * H >- A = A in Ui
 * H >- f = f in y:C -> D
 * H >- g = g in z:E -> F
 *)
axiom functionExtensionality 'H (y:'C -> 'D['y]) (z:'E -> 'F['z]) 'u :
   sequent [squash] { 'H; u: 'A >- ('f 'u) = ('g 'u) in 'B['u] } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- 'f = 'f in y:'C -> 'D['y] } -->
   sequent [squash] { 'H >- 'g = 'g in z:'E -> 'F['z] } -->
   sequent ['ext] { 'H >- 'f = 'g in x:'A -> 'B['x] }

(*
 * H, f: (x:A -> B), J[x] >- T[f] t[f, f a, it]
 * by functionElimination i a y v
 *
 * H, f: (x:A -> B), J[x] >- a = a in A
 * H, f: (x:A -> B), J[x], y: B[a], v: y = f(a) in B[a] >- T[f] ext t[f, y, v]
 *)
axiom functionElimination 'H 'J 'f 'a 'y 'v :
   sequent [squash] { 'H; f: x:'A -> 'B['x]; 'J['f] >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H; f: x:'A -> 'B['x]; 'J['f]; y: 'B['a]; v: 'y = ('f 'a) in 'B['a] >- 'T['f] } -->
   sequent ['ext] { 'H; f: x:'A -> 'B['x]; 'J['f] >- 'T['f] }

(*
 * H >- (f1 a1) = (f2 a2) in B[a1]
 * by applyEquality (x:A -> B[x])
 *
 * H >- f1 = f2 in x:A -> B[x]
 * H >- a1 = a2 in A
 *)
axiom applyEquality 'H (x:'A -> 'B['x]) :
   sequent [squash] { 'H >- 'f1 = 'f2 in x:'A -> 'B['x] } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- ('f1 'a1) = ('f2 'a2) in 'B['a1] }

(*
 * H >- a1:A1 -> B1 <= a2:A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H, a: A1 >- B1[a] <= B2[a]
 *)
axiom functionSubtype 'H 'a :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['prop] { 'H >- subtype{ (a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2]) } }

(*
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; J[x] >- T[x]
 * by function_subtypeElimination i
 *
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; y: A2 <= A1; z: a:A2 -> B2[a] <= B1[a]; J[x] >- T[x]
 *)
axiom function_subtypeElimination 'H 'J 'x 'y 'z 'a :
   sequent { 'H;
             x: subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])};
             'J['x];
             y: subtype{'A2; 'A1};
             z: a:'A2 -> subtype{'B1['a]; 'B2['a]}
             >- 'T['x]
           } -->
   sequent { 'H; x: subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])}; 'J['x] >- 'T['x] }

(*
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; J[x] >- T[x]
 * by function_equalityElimination
 *
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; y: A1 = A2 in Ui; z: a:A1 -> B1[a] = B2[a] in Ui; J[x] >- T[x]
 *)
axiom function_equalityElimination 'H 'J 'x 'y 'z 'a :
   sequent { 'H;
             x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[@i:l];
             'J['x];
             y: 'A1 = 'A2 in univ[@i:l];
             z: a:'A1 -> ('B1['a] = 'B2['a] in univ[@i:l])
             >- 'T['x]
           } -->
   sequent { 'H; x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[@i:l]; 'J['x] >- 'T['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_dfunT : int -> tactic
val eqcd_dfunT : tactic

(*
 * $Log$
 * Revision 1.7  1998/07/02 18:37:26  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.6  1998/06/23 22:12:29  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 * Revision 1.5  1998/05/28 13:47:26  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.4  1998/04/22 22:44:39  jyh
 * *** empty log message ***
 *
 * Revision 1.3  1997/08/07 19:43:51  jyh
 * Updated and added Lori's term modifications.
 * Need to update all pattern matchings.
 *
 * Revision 1.2  1997/08/06 16:18:25  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:08  jyh
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
 * Revision 1.7  1996/10/23 15:18:05  jyh
 * First working version of dT tactic.
 *
 * Revision 1.6  1996/09/02 19:37:19  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.5  1996/05/21 02:16:38  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.4  1996/04/11 13:33:52  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.3  1996/03/30 01:37:13  jyh
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
