(*
 * We define an equality on sets.
 * The normal intensional equality ('s1 = 's2 in set) is
 * not sufficient, because it is not a small type (it is in U2).
 *
 * We define and extensional equality by induction
 * on the sets.
 *)

include Czf_itt_pre_set

open Refiner.Refiner.TermType

open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare eq_inner{'s1; 's2}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reduce_eq_inner : eq_inner{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((all y1 : 'T1. exst y2: 'T2. eq_inner{.'f1['y1]; .'f2['y2]})
    & (all y2 : 'T2. exst y1: 'T1. eq_inner{.'f1['y1]; .'f2['y2]}))

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Membership in a universe.
 *)
axiom eq_inner_equality1 'H :
   sequent [squash] { 'H >- is_pre_set{'s1} } -->
   sequent [squash] { 'H >- is_pre_set{'s2} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} = eq_inner{'s1; 's2} in univ[1:l] }

(*
 * Membership in a universe.
 *)
axiom eq_inner_type 'H :
   sequent [squash] { 'H >- is_pre_set{'s1} } -->
   sequent [squash] { 'H >- is_pre_set{'s2} } -->
   sequent ['ext] { 'H >- "type"{eq_inner{'s1; 's2}} }

(*
 * More general equality in a universe.
 *)
axiom eq_inner_equality2 'H :
   sequent [squash] { 'H >- 's1 = 's3 in pre_set } -->
   sequent [squash] { 'H >- 's2 = 's4 in pre_set } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} = eq_inner{'s3; 's4} in univ[1:l] }

(*
 * Equivalence relation rules.
 *)
axiom eq_inner_ref 'H :
   sequent [squash] { 'H >- is_pre_set{'s1} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's1} }

axiom eq_inner_sym 'H :
   sequent [squash] { 'H >- is_pre_set{'s1} } -->
   sequent [squash] { 'H >- is_pre_set{'s2} } -->
   sequent ['ext] { 'H >- eq_inner{'s2; 's1} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} }

axiom eq_inner_trans 'H 's2 :
   sequent [squash] { 'H >- is_pre_set{'s1} } -->
   sequent [squash] { 'H >- is_pre_set{'s2} } -->
   sequent [squash] { 'H >- is_pre_set{'s3} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} } -->
   sequent ['ext] { 'H >- eq_inner{'s2; 's3} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's3} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Equality relations.
 *)
val eqInnerRefT : tactic
val eqInnerSymT : tactic
val eqInnerTransT : term -> tactic

(*
 * $Log$
 * Revision 1.2  1998/07/21 22:45:28  jyh
 * Added NL toploop so that we can compile NL native code.
 *
 * Revision 1.1  1998/07/14 15:43:16  jyh
 * Intermediate version with auto tactic.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
