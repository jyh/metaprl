(*
 * Membership over the extensional equality.
 *)

include Czf_itt_eq

open Refiner.Refiner.Term
open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Conversionals
open Sequent
open Var

open Itt_rfun
open Itt_logic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare member{'x; 'y}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

primrw unfold_member : member{'x; 'y} <-->
   ((isset{'x} & isset{'y}) & set_ind{'y; T, f, g. exst t: 'T. eq{'x; .'f 't}})

interactive_rw reduce_member : member{'x; collect{'T; y. 'f['y]}} <-->
   ((isset{'x} & isset{collect{'T; y. 'f['y]}}) & (exst t: 'T. eq{'x; .'f['t]}))

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform member_df : mode[prl] :: parens :: "prec"[prec_apply] :: member{'x; 't} =
   slot{'x} " " Nuprl_font!member " " slot{'t}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Membership judgment is also a type.
 *)
interactive member_type 'H :
   sequent ['ext] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- "type"{member{'s1; 's2}} }

(*
 * Sets contain only sets.
 *)
interactive elem_isset 'H 'y :
   sequent ['ext] { 'H >- member{'x; 'y} } -->
   sequent ['ext] { 'H >- isset{'x} }

(*
 * Only sets have elements.
 *)
interactive set_isset 'H 'x :
   sequent ['ext] { 'H >- member{'x; 'y} } -->
   sequent ['ext] { 'H >- isset{'y} }

(*
 * Functionality.
 *)
interactive member_fun_left 'H 's1 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- member{'s1; 's3} } -->
   sequent ['ext] { 'H >- member{'s2; 's3} }

interactive member_fun_right 'H 's1 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- member{'s3; 's1} } -->
   sequent ['ext] { 'H >- member{'s3; 's2} }

interactive member_fun 'H :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. member{'f1['z]; 'f2['z]}} }

(*
 * Set extensionality.
 *)
interactive set_ext 'H 'x 'y :
   sequent ['ext] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H; x: set; y: member{'x; 's1} >- member{'x; 's2} } -->
   sequent ['ext] { 'H; x: set; y: member{'x; 's2} >- member{'x; 's1} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * H >- member{a; t} type
 *)
let d_member_typeT i p =
   if i = 0 then
      member_type (Sequent.hyp_count p) p
   else
      raise (RefineError ("d_member_typeT", StringError "no elimination rule"))

let member_type_term = << "type"{member{'a; 't}} >>

let d_resource = d_resource.resource_improve d_resource (member_type_term, d_member_typeT)

(*
 * Functionality.
 *)
let d_member_funT i p =
   if i = 0 then
      member_fun (hyp_count p) p
   else
      raise (RefineError ("d_member_funT", StringError "no elimination form"))

let member_fun_term = << "fun_prop"{z. member{'s1['z]; 's2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (member_fun_term, d_member_funT)

(*
 * Membership.
 *)
let memberOfT t p =
   elem_isset (hyp_count p) t p

let setOfT t p =
   set_isset (hyp_count p) t p

(*
 * Prove equality by extensionality.
 *)
let setExtT p =
   let u, v = maybe_new_vars2 p "u" "v" in
      (set_ext (hyp_count p) u v
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "wf";
               addHiddenLabelT "main";
               addHiddenLabelT "main"]) p

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
