(*
 * Empty set.
 *)

include Czf_itt_member

open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare sep{'s; x. 'P['x]}
declare restricted{z. 'P['z]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reduce_sep : sep{collect{'T; x. 'f['x]}; z. 'P['z]} <-->
   collect{. "prod"{'T; t. 'P['f['t]]}; w. 'f[fst{'w}]}

(*
 * A restricted formula has the separation property.
 *)
rewrite unfold_restricted : restricted{z. 'P['z]} <-->
   (exst P2: (set -> univ[1:l]). (fun_prop{z. 'P2 'z} & (all z: set. "iff"{. 'P2 'z; 'P['z]})))

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Validity of separation.
 *)
axiom sep_isset 'H 'z :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; z: set >- 'P['z] = 'P['z] in univ[1:l] } -->
   sequent ['ext] { 'H >- isset{.sep{'s; x. 'P['x]}} }

(*
 * Intro form.
 *)
axiom sep_intro2 'H :
   sequent [squash] { 'H; w: set >- 'P['w] = 'P['w] in univ[1:l] } -->
   sequent ['ext] { 'H >- fun_prop{z. 'P['z]} } -->
   sequent ['ext] { 'H >- member{'x; 's} } -->
   sequent ['ext] { 'H >- 'P['x] } -->
   sequent ['ext] { 'H >- member{'x; sep{'s; z. 'P['z]}} }

(*
 * Elim exposes the computational content.
 *)
axiom sep_elim 'H 'J 'u 'v 'z :
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- isset{'s} } -->
   sequent [squash] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w]; z: set >- 'P['z] = 'P['z] in univ[1:l] } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- fun_prop{z. 'P['z]} } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w]; u: member{'x; 's}; v: 'P['x] >- 'T['w] } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- 'T['w] }

(*
 * Functionality properties.
 *)
axiom sep_fun_set 'H :
   sequent ['ext] { 'H; w: set >- 'P['w] = 'P['w] in univ[1:l] } -->
   sequent ['ext] { 'H >- fun_prop{z. 'P['z]} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- eq{sep{'s1; z. 'P['z]}; sep{'s2; z. 'P['z]}} }

axiom sep_fun 'H 'u 'v :
   sequent ['ext] { 'H; u: set; v: set >- 'P['u; 'v] = 'P['u; 'v] in univ[1:l] } -->
   sequent ['ext] { 'H; u: set >- fun_prop{z. 'P['z; 'u]} } -->
   sequent ['ext] { 'H; u: set >- fun_prop{z. 'P['u; 'z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 's['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. sep{'s['z]; x. 'P['x; 'z]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
