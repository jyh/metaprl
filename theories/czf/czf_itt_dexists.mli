(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_set
include Czf_itt_sep

open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "exists"{'T; x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_dexists : "exists"{'s; x. 'A['x]} <-->
   set_ind{'s; a, f, g. "prod"{'a; x. 'A['f 'x]}}

rewrite reduce_dexists : "exists"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T *'A['f['t]])

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
axiom dexists_type 'H 'y :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."exists"{'s; x. 'A['x]}} }


(*
 * Well formedness.
 *)
axiom dexists_wf 'H 'y :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H; y: set>- wf{'A['y]} } -->
   sequent ['ext] { 'H >- wf{."exists"{'s; x. 'A['x]} } }

(*
 * Intro.
 *)
axiom dexists_intro 'H 'z 'w :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H; w: set >- wf{'A['w]} } -->
   sequent ['ext] { 'H >- member{'z; 's} } -->
   sequent ['ext] { 'H >- 'A['z] } -->
   sequent ['ext] { 'H >- "exists"{'s; x. 'A['x]} }

axiom dexists_intro2 'H 'z 'w :
   sequent ['ext] { 'H; w: set >- wf{'A['w]} } -->
   sequent ['ext] { 'H >- member{'z; 's} } -->
   sequent ['ext] { 'H >- 'A['z] } -->
   sequent ['ext] { 'H >- "exists"{'s; x. 'A['x]} }

(*
 * Elimination.
 *)
axiom dexists_elim 'H 'J 'x 'z 'v 'w :
   sequent ['ext] { 'H; x: "exists"{'s; y. 'A['y]}; 'J['x] >- isset{'s} } -->
   sequent ['ext] { 'H; x: "exists"{'s; y. 'A['y]}; 'J['x]; z: set >- wf{'A['z]} } -->
   sequent ['ext] { 'H;
                    x: "exists"{'s; y. 'A['y]};
                    'J['x];
                    z: set;
                    v: member{'z; 's};
                    w: 'A['z]
                    >- 'C['x]
                  } -->
   sequent ['ext] { 'H; x: "exists"{'s; y. 'A['y]}; 'J['x] >- 'C['x] }

(*
 * This is a restricted formula.
 *)
axiom dexists_res 'H 'w :
   sequent ['ext] { 'H; w: set >- isset{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- restricted{y. 'B['y; 'w]} } -->
   sequent ['ext] { 'H >- restricted{z. "exists"{'A['z]; y. 'B['y; 'z]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
