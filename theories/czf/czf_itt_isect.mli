(*
 * Intersection of two sets.
 *)

include Czf_itt_set

open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "isect"{'s1; 's2}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_isect : isect{'s1; 's2} <-->
   set_ind{'s1; a1, f1, g1.
      set_ind{'s2; a2, f2, g2.
         collect{.(z: 'a1 * 'a2); x. spread{'x; a, b.

rewrite reduce_union : union{collect{'t1; x1. 'f1['x1]};
                             collect{'t2; x2. 'f2['x2]}} <-->
   collect{.Itt_union!union{'t1; 't2}; x. decide{'x; z. 'f1['z]; z. 'f2['z]}}

val fold_union : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Union is a set.
 *)
axiom union_isset 'H :
   sequent ['ext] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- isset{union{'s1; 's2}} }

(*
 * Membership in a union.
 *)
axiom union_member_intro_left 'H :
   sequent ['ext] { 'H >- member{'x; 's1} } -->
   sequent ['ext] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- member{'x; union{'s1; 's2}} }

axiom union_member_intro_right 'H :
   sequent ['ext] { 'H >- member{'x; 's2} } -->
   sequent ['ext] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- member{'x; union{'s1; 's2}} }

(*
 * This is the elimination form we want,
 * but it requires extensional equality.
axiom union_member_elim 'H 'J :
   sequent ['ext] { 'H; x: member{'y; 's1}; 'J['x] >- 'T['x] } -->
   sequent ['ext] { 'H; x: member{'y; 's2}; 'J['x] >- 'T['x] } -->
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x] >- 'T['x] }
 *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
