(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_all
include Czf_itt_set_ind

open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "dall"{'T; x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_dall : "dall"{'s; x. 'A['x]} <-->
   set_ind{'s; a, f, g. (x: 'a -> 'A['f 'x])}

rewrite reduce_dall : "dall"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T -> 'A['f['t]])

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
axiom dall_type 'H 'y :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."dall"{'s; x. 'A['x]}} }

(*
 * Intro.
 *)
axiom dall_intro 'H 'a 'b :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; a: set >- "type"{'A['a]} } -->
   sequent ['ext] { 'H; a: set; b: member{'a; 's} >- 'A['a] } -->
   sequent ['ext] { 'H >- "dall"{'s; x. 'A['x]} }

(*
 * Elimination.
 *)
axiom dall_elim 'H 'J 'z 'w :
   sequent [squash] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x]; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x] >- fun_prop{w. 'A['w]} } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x] >- member{'z; 's} } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x]; w: 'A['z] >- 'C['x] } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x] >- 'C['x] }

(*
 * This is a restricted formula.
 *)
axiom dall_res2 'H 'w 'x :
   sequent ['ext] { 'H; w: set; x: set >- "type"{'B['w; 'x]} } -->
   sequent ['ext] { 'H >- fun_set{w. 'A['w]} } -->
   sequent ['ext] { 'H >- restricted{z, y. 'B['z; 'y]} } -->
   sequent ['ext] { 'H >- restricted{z. "dall"{'A['z]; y. 'B['z; 'y]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
