(*
 * Binary union.
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

include Itt_tunion
include Itt_bool
include Itt_struct

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
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_dtactic

open Itt_equal
open Itt_struct

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare bunion{'A; 'B}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_bunion

dform bunion_df : parens :: "prec"[prec_bunion] :: bunion{'A; 'B} =
   slot["le"]{'A} `" " cup space slot{'B}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_bunion : bunion{'A; 'B} <-->
                          tunion{bool; x. ifthenelse{'x; 'A; 'B}}

let fold_bunion = makeFoldC << bunion{'A; 'B} >> unfold_bunion

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive bunionEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- bunion{'A1; 'B1} = bunion{'A2; 'B2} in univ[i:l] }

interactive bunionType {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{bunion{'A; 'B}} }

(*
 * Formation.
 *)
interactive bunionFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * Membership.
 *)
interactive bunionMemberEqualityLeft {| intro_resource [SelectOption 1]; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'x = 'y in 'A } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- 'x = 'y in bunion{'A; 'B} }

interactive bunionMemberEqualityRight {| intro_resource [SelectOption 2]; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'x = 'y in 'B } -->
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- 'x = 'y in bunion{'A; 'B} }

(*
 * Elimination.
 *)
interactive bunionElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'y 'z :
   [main] sequent ['ext] { 'H; x: bunion{'A; 'B}; 'J['x]; y: 'A; z: 'y = 'x in bunion{'A; 'B} >- 'C['x] } -->
   [main] sequent ['ext] { 'H; x: bunion{'A; 'B}; 'J['x]; y: 'B; z: 'y = 'x in bunion{'A; 'B} >- 'C['x] } -->
   sequent ['ext] { 'H; x: bunion{'A; 'B}; 'J['x] >- 'C['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
