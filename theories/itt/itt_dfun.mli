(*
 * Dependent functions.
 *
 *)

include Itt_equal
include Itt_rfun

open Refiner.Refiner.Term

open Tacticals

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reduceEta (x: 'A -> 'B['x]) : ('f = 'f in (x: 'A -> 'B['x])) -->
   lambda{x. 'f 'x} <--> 'f

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
 * Typehood.
 *)
axiom functionType 'H 'x :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H; x: 'A1 >- "type"{'B1['x]} } -->
   sequent ['ext] { 'H >- "type"{. a1:'A1 -> 'B1['a1] } }

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
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
