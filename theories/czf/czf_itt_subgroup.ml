(*!
 * @spelling{subgroup}
 *
 * @begin[doc]
 * @theory[Czf_itt_subgroup]
 *
 * The @tt{Czf_itt_subgroup} module defines subgroups.
 * A subgroup of a group $g$ is a group whose carrier
 * is a subset of $g$ and who shares the same binary
 * operation as $g$.
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
 * Copyright (C) 2002 Xin Yu, Caltech
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
 * Author: Xin Yu
 * @email{xiny@cs.caltech.edu}
 * @end[license]
 *)

(*! @doc{@parents} *)
include Czf_itt_group
include Czf_itt_subset
include Czf_itt_isect
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Sequent
open Tactic_type.Tacticals
open Var
open Mptop

open Base_dtactic
open Base_auto_tactic

let _ =
   show_loading "Loading Czf_itt_subgroup%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare subgroup{'s; 'g}
(*! @docoff *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * A group $s$ is a subgroup of group $g$ if the carrier of $s$
 * is a subset of that of $g$ and the operation of $s$ is the same
 * as that of $g$.
 * @end[doc]
 *)
prim_rw unfold_subgroup : subgroup{'s; 'g} <-->
   (group{'s} & group{'g} & subset{car{'s}; car{'g}} & (all a: set. all b: set. (mem{'a; car{'s}} => mem{'b; car{'s}} => eq{op{'s; 'a; 'b}; op{'g; 'a; 'b}})))
(*! @docoff *)

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform subgroup_df : except_mode[src] :: subgroup{'s; 'g} =
   `"subgroup(" slot{'s} `"; " slot{'g} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Typehood}
 *
 * The $@subgroup{s; g}$ is well-formed if its arguments are labels.
 * @end[doc]
 *)
interactive subgroup_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- "type"{subgroup{'s; 'g}} }

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * The proposition $@subgroup{s; g}$ is true if it is well-formed,
 * $s$ and $g$ are groups, $@car{s}$ is a subset of $@car{g}$, and
 * $@op{s; a; b}$ is defined as $@op{g; a; b}$ for $a, b @in @car{s}$.
 * @end[doc]
 *)
interactive subgroup_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'s} } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- subset{car{'s}; car{'g}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: mem{'a; car{'s}}; y: mem{'b; car{'s}} >- eq{op{'s; 'a; 'b}; op{'g; 'a; 'b}} } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} }

(*!
 * @begin[doc]
 * @thysubsection{Properties}
 *
 * If $s$ is a subgroup of $g$, then
 * @begin[enumerate]
 * @item{$s$ is closed under the binary operation of $g$.}
 * @item{the identity of $s$ is also an identity of $g$.}
 * @item{the inverse of $a @in @car{s}$ is also the inverse of $a$ in $g$.}
 * @end[enumerate]
 * @end[doc]
 *)
interactive subgroup_op {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent ['ext] { 'H >- mem{'a; car{'s}} } -->
   sequent ['ext] { 'H >- mem{'b; car{'s}} } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} } -->
   sequent ['ext] { 'H >- mem{op{'g; 'a; 'b}; car{'s}} }

interactive subgroup_id1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} } -->
   sequent ['ext] { 'H >- eq{id{'s}; id{'g}} }

interactive subgroup_id2 {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} } -->
   sequent ['ext] { 'H >- mem{id{'g}; car{'s}} }

interactive subgroup_inv1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'s}} } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} } -->
   sequent ['ext] { 'H >- eq{inv{'s; 'a}; inv{'g; 'a}} }

interactive subgroup_inv2 {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'s}} } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} } -->
   sequent ['ext] { 'H >- mem{inv{'g; 'a}; car{'s}} }

(*!
 * @begin[doc]
 * @thysubsection{Theorems}
 *
 * The intersection of subgroups $h_1$ and $h_2$ of a group $g$ is
 * again a subgroup of $g$.
 * @end[doc]
 *)
interactive subgroup_isect 'H 'h1 'h2 :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 'h1 IN label } -->
   sequent [squash] { 'H >- 'h2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent ['ext] { 'H >- subgroup{'h1; 'g} } -->
   sequent ['ext] { 'H >- subgroup{'h2; 'g} } -->
   sequent ['ext] { 'H >- group{'h} } -->
   sequent ['ext] { 'H >- equal{car{'h}; ."isect"{car{'h1}; car{'h2}}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: mem{'a; car{'h}}; y: mem{'b; car{'h}} >- eq{op{'h; 'a; 'b}; op{'h1; 'a; 'b}} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g} }

(*! @docoff *)
(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*!
 * @begin[doc]
 * @tactics
 *
 * @begin[description]
 * @item{@tactic[subgroupIsectT];
 *    The tactic applies the @hrefrule[subgroup_isect] rule
 *    and proves $h$ is a subgroup of $g$ if it is the
 *    intersection of two subgroups of $g$.}
 * @end[description]
 * @docoff
 * @end[doc]
 *)
let subgroupIsectT t1 t2 p =
   subgroup_isect (hyp_count_addr p) t1 t2 p

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
