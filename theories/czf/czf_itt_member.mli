(*
 * Membership over the extensional equality.
 *)

include Czf_itt_eq

open Refiner.Refiner.Term

open Tacticals
open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare member{'x; 'y}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

rewrite unfold_member : member{'x; 'y} <-->
   ((isset{'x} & isset{'y}) & set_ind{'y; T, f, g. exst t: 'T. eq{'x; .'f 't}})

rewrite reduce_member : member{'x; collect{'T; y. 'f['y]}} <-->
   ((isset{'x} & isset{collect{'T; y. 'f['y]}}) & (exst t: 'T. eq{'x; .'f['t]}))

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Membership judgment is also a type.
 *)
axiom member_type 'H :
   sequent ['ext] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- "type"{member{'s1; 's2}} }

(*
 * Sets contain only sets.
 *)
axiom elem_isset 'H 'y :
   sequent ['ext] { 'H >- member{'x; 'y} } -->
   sequent ['ext] { 'H >- isset{'x} }

(*
 * Only sets have elements.
 *)
axiom set_isset 'H 'x :
   sequent ['ext] { 'H >- member{'x; 'y} } -->
   sequent ['ext] { 'H >- isset{'y} }

(*
 * Functionality.
 *)
axiom member_fun_left 'H 's1 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- member{'s1; 's3} } -->
   sequent ['ext] { 'H >- member{'s2; 's3} }

axiom member_fun_right 'H 's1 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- member{'s3; 's1} } -->
   sequent ['ext] { 'H >- member{'s3; 's2} }

axiom member_fun 'H :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. member{'f1['z]; 'f2['z]}} }

(*
 * Set extensionality.
 *)
axiom set_ext 'H 'x 'y :
   sequent ['ext] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H; x: set; y: member{'x; 's1} >- member{'x; 's2} } -->
   sequent ['ext] { 'H; x: set; y: member{'x; 's2} >- member{'x; 's1} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * member{'x; 'y} => isset{'x}
 *)
val memberOfT : term -> tactic

(*
 * member{'x; 'y} => isset{'y}
 *)
val setOfT : term -> tactic

(*
 * Apply seq extensionality.
 *)
val setExtT : tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
