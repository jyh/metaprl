(*!
 * @begin[doc]
 * @module[Itt_subset]
 *
 * The @tt[Itt_subset] module provides the set-theoretic definition of 
 * @emph{subset}. A type $T_1$ is a subset of a type $T_2$,
 * $@subset{T_1; T_2}$, if $T_1$ is a subtype of $T_2$, if any two equal
 * elements in $T_2$ are either both in $T_1$ or both not in $T_1$,
 * and for any two elements of $T_1$, if they are equal in $T_2$,
 * then they are also equal in $T_1$. For example, $@int @subseteq @int_2$,
 * but not $@subset{@int; @int_2}$.
 *
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * Author: Jason Hickey @email{jyh@cs.caltech.edu}
 * Modified by: Xin Yu @email{xiny@cs.caltech.edu}
 *
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Itt_subtype
extends Itt_struct
extends Itt_logic
extends Itt_set
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

open Itt_struct
open Itt_logic
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_subset%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * @end[doc]
 *)
define unfold_subset : "subset"{'A; 'B} <-->
   "subtype"{'A; 'B} & (all a: 'A. all b: 'A. (('a = 'b in 'B) => ('a = 'b in 'A))) & "subtype"{{b: 'B | exst a: 'A. 'b = 'a in 'B}; 'A}
(*! @docoff *)

let fold_subset = makeFoldC << "subset"{'A; 'B} >> unfold_subset

let subset_term = << 'A subset 'B >>
let subset_opname = opname_of_term subset_term
let is_subset_term = is_dep0_dep0_term subset_opname
let dest_subset = dest_dep0_dep0_term subset_opname
let mk_subset_term = mk_dep0_dep0_term subset_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform subset_df1 : except_mode[src] :: parens :: "prec"[prec_subtype] :: "subset"{'A; 'B} =
   math_subset{'A; 'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive subset_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   [wf] sequent [squash] { 'H; x: 'A >- 'x IN 'B } -->
   sequent ['ext] { 'H >- "type"{"subset"{'A; 'B}} }

interactive subset_intro {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   [wf] sequent [squash] { 'H; x: 'A >- 'x IN 'B } -->
   [main] sequent [squash] {'H; a: 'B; b: 'A; u: 'a = 'b in 'B >- 'a in 'A } -->
   [main] sequent [squash] { 'H; a: 'A; b: 'A; u: 'a = 'b in 'B >- 'a = 'b in 'A } -->
   sequent ['ext] { 'H >- "subset"{'A; 'B} }

interactive set_subset_intro {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; x: 'A >- 'P['x] } -->
   sequent ['ext] { 'H >- "subset"{{a: 'A | 'P['a]}; 'A } }

interactive subset_ref {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- 'A subset 'A }

(*
interactive subset_trans 'H 'B:
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   [wf] sequent [squash] { 'H >- "type"{'C} } -->
   sequent ['ext] { 'H >- "subset"{'A; 'B} } -->
   sequent ['ext] { 'H >- "subset"{'B; 'C} } -->
   sequent ['ext] { 'H >- "subset"{'A; 'C} }
*)

(*
interactive set_subset_elim1 {| elim [] |} 'H 'J :
   [wf] sequent [squash] { 'H; x: "subset"{'A; 'B}; 'J['x] >- 'a = 'b in 'A } -->
   sequent ['ext] { 'H; x: "subset"{'A; 'B}; 'J['x] >- 'a = 'b in 'B }
*)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
