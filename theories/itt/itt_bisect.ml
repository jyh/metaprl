(*
 * Binary intersection.
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

include Itt_isect
include Itt_bool

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals

open Itt_equal

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare bisect{'A; 'B}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_bisect

dform bisect_df : parens :: "prec"[prec_bisect] :: bisect{'A; 'B} =
   slot["le"]{'A} `" " cap space slot{'B}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_bisect : bisect{'A; 'B} <-->
                          "isect"{bool; x. ifthenelse{'x; 'A; 'B}}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive bisectEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- bisect{'A1; 'B1} = bisect{'A2; 'B2} in univ[i:l] }

interactive bisectMember {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'A} } -->
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'B} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; bisect{'A; 'B}} }

interactive bisectType {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{bisect{'A; 'B}} }

(*
 * Formation.
 *)
interactive bisectFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * Membership.
 *)
interactive bisectMemberEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'x = 'y in 'A } -->
   [wf] sequent [squash] { 'H >- 'x = 'y in 'B } -->
   sequent ['ext] { 'H >- 'x = 'y in bisect{'A; 'B} }

interactive bisectMemberMember {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{'A; 'x} } -->
   [wf] sequent [squash] { 'H >- member{'B; 'x} } -->
   sequent ['ext] { 'H >- member{bisect{'A; 'B}; 'x} }

(*
 * Elimination.
 *)
interactive bisectEliminationLeft 'H 'J 'y 'z :
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x]; y: 'A; z: 'y = 'x in 'A >- 'C['x] } -->
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x] >- 'C['x] }

interactive bisectEliminationRight 'H 'J 'y 'z :
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x]; y: 'B; z: 'y = 'x in 'B >- 'C['x] } -->
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x] >- 'C['x] }

(*
 * D tactic.
 *)
let elim_bisectT i p =
   let sel = get_sel_arg p in
   let tac =
      if sel = 1 then
         bisectEliminationLeft
      else
         bisectEliminationRight
   in
   let j, k = Sequent.hyp_indices p i in
   let u, v = maybe_new_vars2 p "u" "v" in
      tac j k u v p

let bisect_term = << bisect{'A; 'B} >>

let elim_resource = Mp_resource.improve elim_resource (bisect_term, elim_bisectT)

(*
 * Subtyping.
 *)
interactive bisectSubtypeLeft 'H :
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent [squash] { 'H >- subtype{'A; 'C} } -->
   sequent ['ext] { 'H >- subtype{bisect{'A; 'B}; 'C} }

interactive bisectSubtypeRight 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- subtype{'B; 'C} } -->
   sequent ['ext] { 'H >- subtype{bisect{'A; 'B}; 'C} }

interactive bisectSubtypeBelow 'H :
   sequent [squash] { 'H >- subtype{'C; 'A} } -->
   sequent [squash] { 'H >- subtype{'C; 'B} } -->
   sequent ['ext] { 'H >- subtype{'C; bisect{'A; 'B}} }

(*
 * Subtyping.
 *)
let intro_bisect_aboveT p =
   let j = get_sel_arg p in
   let tac =
      if j = 1 then
         bisectSubtypeLeft
      else
         bisectSubtypeRight
   in
      tac (Sequent.hyp_count_addr p) p

let bisect_above_term = << subtype{bisect{'A; 'B}; 'C} >>

let intro_resource = Mp_resource.improve intro_resource (bisect_above_term, intro_bisect_aboveT)

let intro_bisect_belowT p =
   bisectSubtypeBelow (Sequent.hyp_count_addr p) p

let bisect_below_term = << subtype{'C; bisect{'A; 'B}} >>

let intro_resource = Mp_resource.improve intro_resource (bisect_below_term, intro_bisect_belowT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
