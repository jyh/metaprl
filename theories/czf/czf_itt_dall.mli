(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_set
include Czf_itt_sep

open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "all"{'T; x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_dall : "all"{'s; x. 'A['x]} <-->
   set_ind{'s; a, f, g. "fun"{'a; x. 'A['f 'x]}}

rewrite reduce_dall : "all"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T -> 'A['f['t]])

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
axiom dall_type 'H 'y :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."all"{'s; x. 'A['x]}} }

(*
 * Well formedness.
 *)
axiom dall_wf 'H 'y :
   sequent ['ext] { 'H >- isset{'T} } -->
   sequent ['ext] { 'H; y: set >- wf{'A['y]} } -->
   sequent ['ext] { 'H >- wf{."all"{'T; x. 'A['x]} } }

(*
 * Intro.
 *)
axiom dall_intro 'H 'a 'b :
   sequent ['ext] { 'H >- isset{'T} } -->
   sequent ['ext] { 'H; a: set >- wf{'A['a]} } -->
   sequent ['ext] { 'H; a: set; b: member{'a; 'T} >- 'A['a] } -->
   sequent ['ext] { 'H >- "all"{'T; x. 'A['x]} }

(*
 * Elimination.
 *)
axiom dall_elim 'H 'J 'x 'z 'w 'u :
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x]; u: set >- wf{'A['u]} } -->
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x] >- member{'z; 'T} } -->
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x]; w: 'A['z] >- 'C['x] } -->
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x] >- 'C['x] }

(*
 * This is a restricted formula.
 *)
axiom dall_res 'H 'w :
   sequent ['ext] { 'H; w: set >- isset{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- restricted{y. 'B['y; 'w]} } -->
   sequent ['ext] { 'H >- restricted{z. "all"{'A['z]; y. 'B['y; 'z]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
