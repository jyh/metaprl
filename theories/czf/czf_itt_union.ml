(*!
 * @begin[doc]
 * @theory[Czf_itt_union]
 *
 * The @tt{Czf_itt_union} module gives two definitions of
 * set unions.  The $@union{s_1; s_2}$ is the binary union
 * of two sets $s_1$ and $s_2$.  The elements of the binary
 * union include the elements in $s_1$ as well as the elements
 * of $s_2$.  The general union $@union{s}$ represents the
 * union of all the elements in $s$.  A set $x$ is a member of
 * the union $@union{s}$ if it is a member of any element of
 * $s$.
 *
 * The binary union is defined for sets $s_1 = @collect{x_1; T_1; f_1[x_1]}$
 * and $s_2 = @collect{x_2; T_2; f_2[x_2]}$ as a set with the disjoint
 * union index type $@"Itt_comment"!union{T_1; T_2}$ defined in
 * the @hreftheory[Itt_union] module.
 *
 * $$
 * @begin[array,l]
 * @line{@item{@union{@collect{x_1; T_1; f_1[x_1]}; @collect{x_1; T_1; f_1[x_1]}} @equiv}}
 * @line{@item{@space @space @space
 *    @collect{x; @"Itt_comment"!union{T_1; T_2};
 *       @decide{x; u; f_1[u]; v; f_2[v]}}}}
 * @end[array]
 * $$
 *
 * The definition of the general union $@union{s}$ is more difficult.
 * First, suppose the set $s$ has the form $@collect{x; T; f[x]}$,
 * and that the elements of $s$ have the form $@collect{y; S_x; g_x[y]}$
 * for each term $x$ in the index type $T$.  The index type of the
 * union is formed as the dependent product space $@prod{x; T; S_x}$.
 * Given a pair $(x, y)$ in the index type, the elements are $g_x[y]$.
 * Effectively, the union has the following definition.
 *
 * $$
 * @begin[array,l]
 * @line{@item{@union{@collect{x; T; @lambda{x; @collect{y; S[x]; {g[x; y]}}}}} @equiv}}
 * @line{@item{@space @space @space
 *   @collect{@pair{x; y}; @prod{z; T; S[z]}; {g[x; y]}}}}
 * @end[array]
 * $$
 *
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
include Czf_itt_dexists
include Czf_itt_subset
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
declare "union"{'s1; 's2}
declare "union"{'s1}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The binary union $@union{s_1; s_2}$ is defined by simultaneous
 * induction on the set arguments.  The index type of the result is
 * the disjoint union of their index types.
 * @end[doc]
 *)
prim_rw unfold_bunion : union{'s1; 's2} <-->
   set_ind{'s1; a1, f1, g1.
      set_ind{'s2; a2, f2, g2.
         collect{.Itt_union!union{'a1; 'a2}; x. decide{'x; z. 'f1 'z; z. 'f2 'z}}}}

interactive_rw reduce_bunion : union{collect{'t1; x1. 'f1['x1]};
                                    collect{'t2; x2. 'f2['x2]}} <-->
   collect{.Itt_union!union{'t1; 't2}; x. decide{'x; z. 'f1['z]; z. 'f2['z]}}
(*! @docoff *)

let fold_bunion = makeFoldC << union{'s1; 's2} >> unfold_bunion

let resource reduce +=
   << union{collect{'t1; x1. 'f1['x1]}; collect{'t2; x2. 'f2['x2]}} >>, reduce_bunion

(*!
 * @begin[doc]
 * The general union is formed by a nested induction on the
 * set argument.  This term formalizes the informal discussion
 * above.
 * @end[doc]
 *)
prim_rw unfold_union : union{'s} <-->
   set_ind{'s; a1, f1, g1.
      collect{.(x: 'a1 * set_ind{.'f1 'x; a2, f2, g2. 'a2});
         y. spread{'y; u, v. set_ind{.'f1 'u; a3, f3, g3. 'f3 'v}}}}
(*! @docoff *)

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform union_df1 : parens :: "prec"[prec_or] :: union{'s1; 's2} =
   slot{'s1} " " cup `"s " slot{'s2}

dform union_df2 : parens :: "prec"[prec_or] :: union{'s} =
   cup `"s " slot{'s}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Well-formedness}
 *
 * Both forms of union are well-formed if their arguments
 * are sets.
 * @end[doc]
 *)
interactive bunion_isset {| intro_resource [] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- isset{union{'s1; 's2}} }

interactive union_isset {| intro_resource [] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- isset{union{'s1}} }

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * The binary union $@union{s_1; s_2}$ has two membership introduction forms
 * for an argument set $x$; the set $x$ may be a member of $s_1$ or it may
 * be a member of $s_2$.
 * @end[doc]
 *)
interactive bunion_member_intro_left {| intro_resource [SelectOption 1] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'x} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'x; 's1} } -->
   sequent ['ext] { 'H >- mem{'x; union{'s1; 's2}} }

interactive bunion_member_intro_right {| intro_resource [SelectOption 2] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'x} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'x; 's2} } -->
   sequent ['ext] { 'H >- mem{'x; union{'s1; 's2}} }

(*!
 * @begin[doc]
 * @noindent
 * A set $x$ is in the general union $@union{s}$ if there is some
 * element $@mem{y; s}$ for which $@mem{x; y}$.
 * @end[doc]
 *)
interactive union_member_intro {| intro_resource [] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'x} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- dexists{'s; y. mem{'x; 'y}} } -->
   sequent ['ext] { 'H >- mem{'x; union{'s}} }

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * @noindent
 * The elimination form for membership in the binary union
 * performs a case analysis on membership in the two sets in
 * the binary union.
 * @end[doc]
 *)
interactive bunion_member_elim {| elim_resource [] |} 'H 'J :
   ["wf"] sequent [squash] { 'H; x: mem{'y; union{'s1; 's2}}; 'J['x] >- isset{'y} } -->
   ["wf"] sequent [squash] { 'H; x: mem{'y; union{'s1; 's2}}; 'J['x] >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H; x: mem{'y; union{'s1; 's2}}; 'J['x] >- isset{'s2} } -->
   sequent ['ext] { 'H; x: mem{'y; union{'s1; 's2}}; 'J['x]; z: mem{'y; 's1} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; union{'s1; 's2}}; 'J['x]; z: mem{'y; 's2} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; union{'s1; 's2}}; 'J['x] >- 'T['x] }

(*!
 * @begin[doc]
 * @noindent
 * The elimination form for the general union $@mem{x; @union{s}}$ produces
 * a witness $@mem{z; y}$ for which $@mem{x; z}$.
 * @end[doc]
 *)
interactive union_member_elim {| elim_resource [] |} 'H 'J :
   ["wf"] sequent [squash] { 'H; x: mem{'y; union{'s}}; 'J['x] >- isset{'y} } -->
   ["wf"] sequent [squash] { 'H; x: mem{'y; union{'s}}; 'J['x] >- isset{'s} } -->
   sequent ['ext] { 'H; x: mem{'y; union{'s}}; 'J['x]; z: set; u: mem{'z; 's}; v: mem{'y; 'z} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; union{'s}}; 'J['x] >- 'T['x] }

(*!
 * @begin[doc]
 * The union types are both functional in their arguments.
 * @end[doc]
 *)
interactive bunion_fun {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- fun_set{z. 's1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 's2['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. union{'s1['z]; 's2['z]}} }

interactive union_fun {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- fun_set{z. 's['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. union{'s['z]}} }
(*! @docoff *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
