(*
 * Simplifications for undependent functions.
 *
 *)

include Tacticals

include Itt_equal
include Itt_dfun

open Refiner.Refiner.TermType

open Tacticals
open Conversionals

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reduceIndependentEta ('A -> 'B) : ('f = 'f in 'A -> 'B) -->
   lambda{x. 'f 'x} <--> 'f

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext A -> B
 * by independentFunctionFormation
 *
 * H >- Ui ext A
 * H >- Ui ext B
 *)
axiom independentFunctionFormation 'H :
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- (A1 -> B1) = (A2 -> B2) in Ui
 * by independentFunctionEquality
 *
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
axiom independentFunctionEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- ('A1 -> 'B1) = ('A2 -> 'B2) in univ[@i:l] }

(*
 * Typehood.
 *)
axiom independentFunctionType 'H 'x :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H; x: 'A1 >- "type"{'B1} } -->
   sequent ['ext] { 'H >- "type"{. 'A1 -> 'B1 } }

(*
 * H >- a:A -> B[a] ext lambda(z. b[z])
 * by lambdaFormation Ui z
 *
 * H >- A = A in Ui
 * H, z: A >- B[z] ext b[z]
 *)
axiom independentLambdaFormation 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H; z: 'A >- 'B } -->
   sequent ['ext] { 'H >- 'A -> 'B }

(*
 * H >- lambda(a1. b1[a1]) = lambda(a2. b2[a2]) in a:A -> B
 * by lambdaEquality Ui x
 *
 * H >- A = A in Ui
 * H, x: A >- b1[x] = b2[x] in B[x]
 *)
axiom independentLambdaEquality 'H 'x :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'A >- 'b1['x] = 'b2['x] in 'B } -->
   sequent ['ext] { 'H >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in 'A -> 'B }

(*
 * H, f: A -> B, J[x] >- T[x]                   ext t[f, f a]
 * by independentFunctionElimination i y
 *
 * H, f: A -> B, J >- A                         ext a
 * H, f: A -> B, J[x], y: B >- T[x]             ext t[f, y]
 *)
axiom independentFunctionElimination 'H 'J 'f 'y :
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'A } -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f]; y: 'B >- 'T['f] } -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'T['f] }

(*
 * Explicit function elimination.
 *)
axiom independentFunctionElimination2 'H 'J 'f 'y 'z 'a :
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f]; y: 'B; z: 'y = ('f 'a) in 'B >- 'T['f] } -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'T['f] }

(*
 * H >- (f1 a1) = (f2 a2) in B[a1]
 * by applyEquality (x:A -> B[x])
 *
 * H >- f1 = f2 in x:A -> B[x]
 * H >- a1 = a2 in A
 *)
axiom independentApplyEquality 'H ('A -> 'B) :
   sequent [squash] { 'H >- 'f1 = 'f2 in 'A -> 'B } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- ('f1 'a1) = ('f2 'a2) in 'B }

(*
 * H >- A1 -> B1 <= A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H >- B1 <= B2
 *)
axiom independentFunctionSubtype 'H :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 -> 'B1); ('A2 -> 'B2) } }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_funT : int -> tactic
val eqcd_funT : tactic

val etaC : term -> conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
