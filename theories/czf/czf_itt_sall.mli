(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_set

open Tacticals
open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "sall"{x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_sall : "sall"{x. 'A['x]} <--> (all x: set. 'A['x])

val fold_sall : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
axiom sall_type 'H 'y :
   sequent ['ext] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."sall"{x. 'A['x]} } }

(*
 * Intro.
 *)
axiom sall_intro 'H 'a :
   sequent ['ext] { 'H; a: set >- 'A['a] } -->
   sequent ['ext] { 'H >- "sall"{x. 'A['x]} }

(*
 * Elimination.
 *)
axiom sall_elim 'H 'J 'x 'z 'w :
   sequent [squash] { 'H; x: "sall"{y. 'A['y]}; 'J['x] >- isset{'z} } -->
   sequent ['ext] { 'H; x: "sall"{y. 'A['y]}; 'J['x]; w: 'A['z] >- 'T['x] } -->
   sequent ['ext] { 'H; x: "sall"{y. 'A['y]}; 'J['x] >- 'T['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
