(*
 * Difference of two types.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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

include Itt_equal
include Itt_logic

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Mp_resource

open Tacticals
open Var

open Itt_equal

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare tsub{'A; 'B}
declare tsub_any

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_tsub

dform tsub_df : mode[prl] :: parens :: "prec"[prec_tsub] :: tsub{'A; 'B} =
   slot["le"]{'A} `" -" space slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
prim tsubEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent [squash] { 'H >- subtype{'B1; 'A1} } -->
   sequent ['ext] { 'H >- tsub{'A1; 'B1} = tsub{'A2; 'B2} in univ[@i:l] } =
   it

prim tsubType 'H :
   sequent [squash] { 'H >- subtype{'B; 'A} } -->
   sequent ['ext] { 'H >- "type"{tsub{'A; 'B}} } =
   it

(*
 * Membership.
 *)
prim tsubMemberEquality 'H 'x :
   sequent [squash] { 'H >- 'x1 = 'x2 in 'A } -->
   sequent [squash] { 'H >- subtype{'B; 'A} } -->
   sequent [squash] { 'H; x: 'x1 = 'x2 in 'B >- "false" } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in tsub{'A; 'B} } =
   it

(*
 * Elimination.
 *)
prim tsubElimination 'H 'J 'x 'y :
   ('t['x; 'y] : sequent ['ext] { 'H; x: 'A; y: ('x = 'x in 'B) => "false"; 'J['x] >- 'C['x] }) -->
   sequent ['ext] { 'H; x: tsub{'A; 'B}; 'J['x] >- 'C['x] } =
   't['x; tsub_any]

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D tactic.
 *)
let d_tsubT i p =
   if i = 0 then
      raise (RefineError ("d_tsubT", StringError "no introduction form"))
   else
      let v, _ = Sequent.nth_hyp p i in
      let v' = maybe_new_vars1 p v in
      let j, k = Sequent.hyp_indices p i in
         tsubElimination j k v v' p

let tsub_term = << tsub{'A; 'B} >>

let d_resource = Mp_resource.improve d_resource (tsub_term, d_tsubT)

let d_tsub_typeT i p =
   if i = 0 then
      (tsubType (Sequent.hyp_count_addr p)
       thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_tsub_typeT", StringError "no elimination form"))

let tsub_type_term = << "type"{tsub{'A; 'B}} >>

let d_resource = Mp_resource.improve d_resource (tsub_type_term, d_tsub_typeT)

(*
 * EQCD.
 *)
let eqcd_tsubT p =
   (tsubEquality (Sequent.hyp_count_addr p)
    thenT addHiddenLabelT "wf") p

let eqcd_resource = Mp_resource.improve eqcd_resource (tsub_term, eqcd_tsubT)

let tsub_equal_term = << tsub{'A1; 'B1} = tsub{'A2; 'B2} in univ[@i:l] >>

let d_resource = Mp_resource.improve d_resource (tsub_equal_term, d_wrap_eqcd eqcd_tsubT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
