(*
 * A normal set-style union of types.
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

include Itt_struct
include Itt_equal
include Itt_set

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Mp_resource

open Base_dtactic
open Tactic_type.Tacticals
open Var

open Itt_struct
open Itt_equal

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare tunion{'A; x. 'B['x]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_tunion

dform isect_df : except_mode[src] :: parens :: "prec"[prec_tunion] :: tunion{'A; x. 'B} =
   cup slot{'x} `":" slot{'A} `"." slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Proof of Ui
 *)
prim tunionFormation 'H 'x 'A :
   [wf] sequent [squash] { 'H >- 'A = 'A in univ[i:l] } -->
   ('B['x] : sequent ['ext] { 'H; x: 'A >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   tunion{'A; x. 'B['x]}

(*
 * Typehood.
 *)
prim tunionEquality {| intro_resource []; eqcd_resource |} 'H 'x :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[i:l] } -->
   sequent ['ext] { 'H >- tunion{'A1; x1. 'B1['x1]} = tunion{'A2; x2. 'B2['x2] } in univ[i:l] } =
   it

prim tunionType {| intro_resource [] |} 'H 'y :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- "type"{tunion{'A; x. 'B['x]}} } =
   it

(*
 * Membership.
 *)
prim tunionMemberEquality {| intro_resource []; eqcd_resource |} 'H 'a 'y :
   [wf] sequent [squash] { 'H >- 'a = 'a in 'A } -->
   [wf] sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   [wf] sequent [squash] { 'H >- 'x1 = 'x2 in 'B['a] } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in tunion{'A; x. 'B['x]} } =
   it

prim tunionMemberFormation {| intro_resource [] |} 'H 'y 'a :
   [wf] sequent [squash] { 'H >- 'a = 'a in 'A } -->
   [wf] sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   [main] ('t : sequent ['ext] { 'H >- 'B['a] }) -->
   sequent ['ext] { 'H >- tunion{'A; x. 'B['x]} } =
   't

(*
 * Elimination.
 *)
prim tunionElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'x 'w 'z :
   sequent [squash] { 'H; x: tunion{'A; y. 'B['y]}; 'J['x]; w: 'A; z: 'B['w] >- 't1['z] = 't2['z] in 'C['z] } -->
   sequent ['ext] { 'H; x: tunion{'A; y. 'B['y]}; 'J['x] >- 't1['x] = 't2['x] in 'C['x] } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let tunion_term = << tunion{'A; x. 'B['x]} >>
let tunion_opname = opname_of_term tunion_term
let mk_tunion_term = mk_dep0_dep1_term tunion_opname
let is_tunion_term = is_dep0_dep1_term tunion_opname
let dest_tunion = dest_dep0_dep1_term tunion_opname

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
