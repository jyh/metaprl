(*
 * Although unit is not strictly necessary,
 * we define it anyway, so we can use it before numbers
 * are defined.
 *
 * Type unit contains one element, it.
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

include Tacticals
include Itt_equal

open Printf
open Mp_debug
open Sequent
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Mp_resource

open Tacticals
open Itt_equal

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_unit%t" eflush

(*
 * incr_debug_level DebugMessage
 * debug_string DebugLoad "Loading itt_void..."
 *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare unit

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform unit_df1 : mode[prl] :: unit = `"Unit"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Unit
 * by unitFormation
 *)
prim unitFormation 'H : : sequent ['ext] { 'H >- univ[@i:l] } = unit

(*
 * H >- Unit = Unit in Ui ext Ax
 * by unitEquality
 *)
prim unitEquality 'H : : sequent ['ext] { 'H >- unit = unit in univ[@i:l] } = it

(*
 * Is a type.
 *)
prim unitType 'H : : sequent ['ext] { 'H >- "type"{unit} } = it

(*
 * H >- Ui ext Unit
 * by unitFormation
 *)
prim unit_memberFormation 'H : : sequent ['ext] { 'H >- unit } = it

(*
 * H >- Unit = Unit in Ui ext Ax
 * by unitEquality
 *)
prim unit_memberEquality 'H : : sequent ['ext] { 'H >- it = it in unit } = it

(*
 * H; i:x:Unit; J >- C
 * by unitElimination i
 * H; i:x:Unit; J[it / x] >- C[it / x]
 *)
prim unitElimination 'H 'J :
   ('t : sequent['ext] { 'H; x: unit; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: unit; 'J['x] >- 'C['x] } =
   't

(*
 * Squash elimination.
 *)
prim unit_squashElimination 'H :
   sequent [squash] { 'H >- unit } -->
   sequent ['ext] { 'H >- unit } =
   it

(*
 * Squiggle equality.
 *)
interactive unitSqequal 'H :
   sequent [squash] { 'H >- 'x = 'y in unit } -->
   sequent ['ext] { 'H >- Perv!"rewrite"{'x; 'y} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Standard term.
 *)
let unit_term = << unit >>

(*
 * D
 *)
let d_unitT i p =
   if i = 0 then
      unit_memberFormation (hyp_count_addr p) p
   else
      let i, j = hyp_indices p i in
         unitElimination i j p

let d_resource = d_resource.resource_improve d_resource (unit_term, d_unitT)

let d_unit_typeT i p =
   if i = 0 then
      unitType (hyp_count_addr p) p
   else
      raise (RefineError ("d_unit_typeT", StringError "no elimination form"))

let unit_type_term = << "type"{unit} >>

let d_resource = d_resource.resource_improve d_resource (unit_type_term, d_unit_typeT)

(*
 * Squiggle reasoning.
 *)
let d_unit_sqequalT i p =
   if i = 0 then
      unitSqequal (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_unit_sqequal", StringError "no elimination form"))

let unit_rewrite_term = << "rewrite"{'e1; it} >>

let d_resource = d_resource.resource_improve d_resource (unit_rewrite_term, d_unit_sqequalT)

(*
 * EqCD.
 *)
let eqcd_unitT p =
   unitEquality (hyp_count_addr p) p

let eqcd_itT p =
   unit_memberEquality (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (unit_term, eqcd_unitT)
let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (it_term, eqcd_itT)
let eqcdT = eqcd_resource.resource_extract eqcd_resource

let equal_unit_term = << unit = unit in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (equal_unit_term, d_wrap_eqcd eqcd_unitT)

let equal_it_term = << it = it in unit >>

let d_resource = d_resource.resource_improve d_resource (equal_it_term, d_wrap_eqcd eqcd_itT)

(************************************************************************
 * SQUASH STABILITY                                                     *
 ************************************************************************)

(*
 * Unit is squash stable.
 *)
let squash_unit p =
   unit_squashElimination (hyp_count_addr p) p

let squash_resource = squash_resource.resource_improve squash_resource (unit_term, squash_unit)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of unit.
 *)
let inf_unit _ decl _ = decl, univ1_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (unit_term, inf_unit)

(*
 * Type of an equality is the type of the equality type.
 *)
let inf_it _ decl _ = decl, unit_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (it_term, inf_it)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
