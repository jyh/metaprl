(*
 * Empty set.
 *)

include Czf_itt_set

open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare sep{'s; x. 'P['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_sep : sep{'s; x. 'P['x]} <-->
   set_ind{'s; T, f, g. collect{."prod"{'T; t. 'P['f 't]}; z. 'f fst{'z}}}

rewrite reduce_sep : sep{collect{'T; x. 'f['x]}; z. 'P['z]} <-->
   collect{. "prod"{'T; t. 'P['f['t]]}; w. 'f[fst{'w}]}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Validity of separation.
 *)
axiom sep_isset 'H 'z :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H; z: set >- small_type{'P['z]} } -->
   sequent ['ext] { 'H >- isset{.sep{'s; x. 'P['x]}} }

(*
 * Intro form.
 *)
axiom sep_intro 'H 'z :
   sequent ['ext] { 'H; z: set >- small_type{'P['z]} } -->
   sequent ['ext] { 'H >- member{'x; 's} } -->
   sequent ['ext] { 'H >- 'P['x] } -->
   sequent ['ext] { 'H >- member{'x; sep{'s; z. 'P['z]}} }

(*
 * Elim exposes the computational content.
 *)
axiom sep_elim 'H 'J 'u 'v 'z :
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- isset{'s} } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w]; z: set >- small_type{'P['z]} } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w]; u: member{'x; 's}; v: 'P['x] >- 'T['w] } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- 'T['w] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
