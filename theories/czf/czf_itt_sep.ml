(*
 * Empty set.
 *)

include Czf_itt_set

open Printf
open Debug

open Refiner.Refiner.RefineError
open Resource

open Sequent
open Conversionals
open Var

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_sep%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare sep{'s; x. 'P['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_sep : sep{'s; x. 'P['x]} <-->
   set_ind{'s; T, f, g. collect{."prod"{'T; t. 'P['f 't]}; z. 'f fst{'z}}}

interactive_rw reduce_sep : sep{collect{'T; x. 'f['x]}; z. 'P['z]} <-->
   collect{. "prod"{'T; t. 'P['f['t]]}; w. 'f[fst{'w}]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform sep_df : mode[prl] :: sep{'s; x. 'P} =
   szone pushm[3] `"{ " slot{'x} " " Nuprl_font!member " " slot{'s} `" |"
   hspace slot{'P} " " `"}" popm ezone

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Validity of separation.
 *)
interactive sep_isset 'H 'z :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H; z: set >- small_type{'P['z]} } -->
   sequent ['ext] { 'H >- isset{.sep{'s; x. 'P['x]}} }

(*
 * Intro form.
 *)
interactive sep_intro 'H 'z :
   sequent ['ext] { 'H; z: set >- small_type{'P['z]} } -->
   sequent ['ext] { 'H >- member{'x; 's} } -->
   sequent ['ext] { 'H >- 'P['x] } -->
   sequent ['ext] { 'H >- member{'x; sep{'s; z. 'P['z]}} }

(*
 * Elim exposes the computational content.
 *)
interactive sep_elim 'H 'J 'u 'v 'z :
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- isset{'s} } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w]; z: set >- small_type{'P['z]} } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w]; u: member{'x; 's}; v: 'P['x] >- 'T['w] } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- 'T['w] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Typehood.
 *)
let d_sep_setT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         sep_isset (hyp_count p) z p
   else
      raise (RefineError ("d_sep_isset", StringError "no elimination form"))

let sep_isset_term = << isset{sep{'s; x. 'P['x]}} >>

let d_resource = d_resource.resource_improve d_resource (sep_isset_term, d_sep_setT)

(*
 * Membership.
 *)
let d_sep_memberT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         sep_intro (hyp_count p) z p
   else
      let u, v, z = maybe_new_vars3 p "u" "v" "z" in
      let j, k = hyp_indices p i in
         sep_elim j k u v z p

let sep_member_term = << member{'x; sep{'s; y. 'P['y]}} >>

let d_resource = d_resource.resource_improve d_resource (sep_member_term, d_sep_memberT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
