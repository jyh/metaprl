(*
 * Empty set.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

include Czf_itt_member

open Printf
open Mp_debug

open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Sequent
open Tactic_type.Conversionals
open Tactic_type.Tacticals
open Var

open Itt_rfun
open Itt_logic

let _ =
   show_loading "Loading Czf_itt_sep%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare sep{'s; x. 'P['x]}
declare restricted{'P}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_sep : sep{'s; x. 'P['x]} <-->
   set_ind{'s; T, f, g. collect{."prod"{'T; t. 'P['f 't]}; z. 'f fst{'z}}}

interactive_rw reduce_sep : sep{collect{'T; x. 'f['x]}; z. 'P['z]} <-->
   collect{. "prod"{'T; t. 'P['f['t]]}; w. 'f[fst{'w}]}

let reduce_info =
   [<< sep{collect{'T; x. 'f['x]}; z. 'P['z]} >>, reduce_sep]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

(*
 * A restricted formula has the separation property.
 *)
prim_rw unfold_restricted1 : restricted{'P} <-->
   (exst P2: univ[1:l]. iff{'P2; 'P})

prim_rw unfold_restricted : restricted{z. 'P['z]} <-->
   (exst P2: (set -> univ[1:l]). (fun_prop{z. 'P2 'z} & (all z: set. "iff"{. 'P2 'z; 'P['z]})))

prim_rw unfold_restricted3 : restricted{'A; x. 'B['x]} <-->
   (exst P2: ('A -> univ[1:l]).
      ((dfun_prop{'A; x. 'B['x]})
      & (all x: 'A. "iff"{.'P2 'x; 'B['x]})))

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform sep_df : mode[prl] :: sep{'s; x. 'P} =
   szone pushm[3] `"{ " slot{'x} " " Nuprl_font!member " " slot{'s} `" |"
   hspace slot{'P} " " `"}" popm ezone

dform restricted_df : mode[prl] :: parens :: "prec"[prec_quant] :: restricted{'P} =
   slot{'P} `" res"

dform restricted_df : mode[prl] :: parens :: "prec"[prec_quant] :: restricted{z. 'P} =
   Nuprl_font!forall slot{'z} `"." slot{'P} `" res"

dform restricted_df : mode[prl] :: parens :: "prec"[prec_quant] :: restricted{'A; x. 'P} =
   Nuprl_font!forall slot{'x} `":" slot{'A} `"." slot{'P} `" res"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Membership and equality are restricted predicates.
 *)
interactive intro_restricted {| intro_resource [] |} 'H :
   ["wf"] sequent ['ext] { 'H; x: set >- "type"{'P['x]} } -->
   ["wf"] sequent ['ext] { 'H >- fun_prop{x. 'P['x]} } -->
   ["main"] sequent ['ext] { 'H; x: set >- restricted{'P['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'P['x]} }

interactive eq_restricted {| intro_resource [] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- restricted{eq{'s1; 's2}} }

interactive member_restricted {| intro_resource [] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- restricted{member{'s1; 's2}} }

(*
 * Validity of separation.
 *)
interactive sep_isset {| intro_resource [] |} 'H 'z :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; z: set >- 'P['z] = 'P['z] in univ[1:l] } -->
   sequent ['ext] { 'H >- isset{.sep{'s; x. 'P['x]}} }

(*
 * Intro form.
 *)
interactive sep_intro2 {| intro_resource [] |} 'H :
   ["wf"]   sequent [squash] { 'H; w: set >- 'P['w] = 'P['w] in univ[1:l] } -->
   ["wf"]   sequent ['ext] { 'H >- fun_prop{z. 'P['z]} } -->
   ["main"] sequent ['ext] { 'H >- member{'x; 's} } -->
   ["main"] sequent ['ext] { 'H >- 'P['x] } -->
   sequent ['ext] { 'H >- member{'x; sep{'s; z. 'P['z]}} }

(*
 * Elim exposes the computational content.
 *)
interactive sep_elim {| elim_resource [] |} 'H 'J 'u 'v 'z :
   ["wf"]   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- isset{'s} } -->
   ["wf"]   sequent [squash] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w]; z: set >- 'P['z] = 'P['z] in univ[1:l] } -->
   ["wf"]   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- fun_prop{z. 'P['z]} } -->
   ["main"] sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w]; u: member{'x; 's}; v: 'P['x] >- 'T['w] } -->
   sequent ['ext] { 'H; w: member{'x; sep{'s; y. 'P['y]}}; 'J['w] >- 'T['w] }

(*
 * Functionality properties.
 *)
interactive sep_fun {| intro_resource [] |} 'H 'u 'v :
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
