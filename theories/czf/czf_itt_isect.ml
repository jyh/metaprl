(*!
 * @begin[doc]
 * @theory{Czf_itt_isect}
 *
 * The @tt{Czf_itt_isect} module gives defines a binary
 * and general intersection.  The intersection is a @emph{derived} form,
 * the binary intersection is defined with separation:
 *
 * $$@isect{s_1; s_2} @equiv @sep{x; s_1; @mem{x; s_2}}.$$
 *
 * The general intersection is defined over the union type.
 * The elements in the intersection $@isect{s}$ are the elements
 * of the union $@union{s}$ that are also members of all
 * the elements of $s$.
 *
 * $$@isect{s} @equiv @sep{x; @union{s}; @dall{y; s; @mem{x; y}}}$$
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * @email{jyh@cs.cornell.edu}
 * @end[license]
 *)

(*! @doc{@parents} *)
include Czf_itt_union
(*! @docoff *)

open Printf
open Mp_debug

open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Sequent
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Var

open Base_dtactic

open Itt_logic

let _ =
   show_loading "Loading Czf_itt_union%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare "isect"{'s1; 's2}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The intersections are derived from the separation
 * set constructor in the @hreftheory[Czf_itt_sep] module,
 * and the union in the @hreftheory[Czf_itt_union] module.
 * @end[doc]
 *)
prim_rw unfold_bisect : "isect"{'s1; 's2} <--> sep{'s1; x. mem{'x; 's2}}
prim_rw unfold_isect : "isect"{'s} <--> sep{union{'s}; x. dall{'s; y. mem{'x; 'y}}}
(*! @docoff *)

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform isect_df1 : parens :: "prec"[prec_and] :: "isect"{'s1; 's2} =
   slot{'s1} " " cap " " slot{'s2}

dform isect_df2 : parens :: "prec"[prec_and] :: "isect"{'s} =
   cap " " slot{'s}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Well-formedness}
 *
 * Both forms of intersection are well-formed if their arguments are sets.
 * @end[doc]
 *)
interactive bisect_isset {| intro_resource [] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- isset{."isect"{'s1; 's2}} }

interactive isect_isset {| intro_resource [] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- isset{."isect"{'s1}} }

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * The binary intersection $@isect{s_1; s_2}$ requires membership
 * in both sets $s_1$ and $s_2$.
 * @end[doc]
 *)
interactive bisect_member_intro {| intro_resource [] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'x} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'x; 's1} } -->
   sequent ['ext] { 'H >- mem{'x; 's2} } -->
   sequent ['ext] { 'H >- mem{'x; ."isect"{'s1; 's2}} }

(*!
 * @begin[doc]
 * A set $x$ is in the general intersection $@isect{s}$ if
 * $@mem{x; y}$ for all $@mem{y; s}$.
 * @end[doc]
 *)
interactive isect_member_intro {| intro_resource [] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'x} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- mem{'x; union{'s}} } -->
   sequent ['ext] { 'H; y: set; w: mem{'y; 's} >- mem{'x; 'y} } -->
   sequent ['ext] { 'H >- mem{'x; ."isect"{'s}} }

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The elimination form for membership in the binary intersection
 * produces the proofs for membership in both types.
 * @end[doc]
 *)
interactive bisect_member_elim {| elim_resource [] |} 'H 'J :
   ["wf"] sequent [squash] { 'H; x: mem{'y; ."isect"{'s1; 's2}}; 'J['x] >- isset{'y} } -->
   ["wf"] sequent [squash] { 'H; x: mem{'y; ."isect"{'s1; 's2}}; 'J['x] >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H; x: mem{'y; ."isect"{'s1; 's2}}; 'J['x] >- isset{'s2} } -->
   sequent ['ext] { 'H; x: mem{'y; ."isect"{'s1; 's2}}; 'J['x]; z: mem{'y; 's1} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; ."isect"{'s1; 's2}}; 'J['x]; z: mem{'y; 's2} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; ."isect"{'s1; 's2}}; 'J['x] >- 'T['x] }

(*!
 * @begin[doc]
 * The elimination form for the general isect $@mem{x; @isect{s}}$ performs
 * instantiation of of the assumption on a particular set $@mem{z; 's}$.
 * @end[doc]
 *)
interactive isect_member_elim {| elim_resource [] |} 'H 'J 'z :
   ["wf"] sequent [squash] { 'H; x: mem{'y; ."isect"{'s}}; 'J['x] >- isset{'z} } -->
   ["wf"] sequent [squash] { 'H; x: mem{'y; ."isect"{'s}}; 'J['x] >- isset{'y} } -->
   ["wf"] sequent [squash] { 'H; x: mem{'y; ."isect"{'s}}; 'J['x] >- isset{'s} } -->
   sequent ['ext] { 'H; x: mem{'y; ."isect"{'s}}; 'J['x] >- mem{'z; 's} } -->
   sequent ['ext] { 'H; x: mem{'y; ."isect"{'s}}; 'J['x]; w: mem{'y; 'z} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; ."isect"{'s}}; 'J['x] >- 'T['x] }

(*!
 * @begin[doc]
 * The intersection types are both functional in their arguments.
 * @end[doc]
 *)
interactive bisect_fun {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- fun_set{z. 's1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 's2['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. "isect"{'s1['z]; 's2['z]}} }

interactive isect_fun {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- fun_set{z. 's['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. "isect"{'s['z]}} }
(*! @docoff *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
