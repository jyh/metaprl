(*
 * Structural rules.
 *
 *)

include Itt_equal

open Refiner.Refiner.Term

open Tacticals
open Sequent

(*
 * This is just syntax for a binding term.
 * It has no semantic meaning in the type theory.
 *)
declare bind{x. 'T['x]}

(*
 * H; x: A; J >- A ext x
 * by hypothesis
 *)
axiom hypothesis 'H 'J 'x :
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'A }

(*
 * H, x: A, J >- A ext t
 * by thin
 * H, J >- A ext t
 *)
axiom thin 'H 'J :
   sequent ['ext] { 'H; 'J >- 'C } -->
   sequent ['ext] { 'H; x: 'A; 'J >- 'C }

(*
 * H, J >- T ext t[s]
 * by cut S
 * H, J >- S ext s
 * H, x: S, J >- T ext t[x]
 *)
axiom cut 'H 'J 'S 'x :
   sequent ['ext] { 'H; 'J >- 'S } -->
   sequent ['ext] { 'H; x: 'S; 'J >- 'T } -->
   sequent ['ext] { 'H; 'J >- 'T }

(*
 * H >- T
 * by introduction t
 * H >- t = t in T
 *)
axiom introduction 'H 't :
   sequent [squash] { 'H >- 't = 't in 'T } -->
   sequent ['ext] { 'H >- 'T }

(*
 * H >- T1[t1] ext t
 * by substitution (t1 = t2 in T2) lambda(x. T1[x])
 * H >- t1 = t2 in T2
 * H >- T1[t2]
 * H, x: T2 >- T1[x] = T1[x] in type
 *)
axiom substitution 'H ('t1 = 't2 in 'T2) bind{x. 'T1['x]} :
   sequent [squash] { 'H >- 't1 = 't2 in 'T2 } -->
   sequent ['ext] { 'H >- 'T1['t2] } -->
   sequent [squash] { 'H; x: 'T2 >- "type"{'T1['x]} } -->
   sequent ['ext] { 'H >- 'T1['t1] }

(*
 * H, x: A, J >- T
 * by hypothesesReplacement B
 * H, x:B, J >- T
 * H, x: A, J >- A = B in type
 *)
axiom hypReplacement 'H 'J 'B univ[@i:l] :
   sequent ['ext] { 'H; x: 'B; 'J['x] >- 'T['x] } -->
   sequent [squash] { 'H; x: 'A; 'J['x] >- 'A = 'B in univ[@i:l] } -->
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'T['x] }

(*
 * H; x: A[t1]; J[x] >> T1[x] ext t
 * by hypSubstitution (t1 = t2 in T2) bind(x. A[x])
 * H; x: A[t1]; J[x] >> t1 = t2 in T2
 * H; x: A[t2]; J[x] >> T1[x]
 * H, x: A[t1]; J[x]; z: T2 >> A[z] in type
 *)
axiom hypSubstitution 'H 'J ('t1 = 't2 in 'T2) bind{y. 'A['y]} 'z :
   sequent [squash] { 'H; x: 'A['t1]; 'J['x] >- 't1 = 't2 in 'T2 } -->
   sequent ['prop]  { 'H; x: 'A['t2]; 'J['x] >- 'T1['x] } -->
   sequent [squash] { 'H; x: 'A['t1]; 'J['x]; z: 'T2 >- "type"{'A['z]} } -->
   sequent ['prop]  { 'H; x: 'A['t1]; 'J['x] >- 'T1['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val nthHypT : int -> tactic
val thinT : int -> tactic
val thinAllT : int -> int -> tactic
val assertT : term -> tactic
val assertAtT : int -> term -> tactic
val useWitnessT : term -> tactic

val substT : term -> int -> tactic
val hypSubstT : int -> int -> tactic
val revHypSubstT : int -> int -> tactic

val replaceHypT : term -> int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
