(*
 * Binary union.
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

include Itt_tunion
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
open Tacticals
open Conversionals

open Itt_equal

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare bunion{'A; 'B}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_bunion

dform bunion_df : mode[prl] :: parens :: "prec"[prec_bunion] :: bunion{'A; 'B} =
   slot["le"]{'A} `" " cup space slot{'B}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_bunion : bunion{'A; 'B} <-->
                          tunion{bool; x. ifthenelse{'x; 'A; 'B}}

let fold_bunion = makeFoldC << bunion{'A; 'B} >> unfold_bunion

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive bunionEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- bunion{'A1; 'B1} = bunion{'A2; 'B2} in univ[@i:l] }

interactive bunionType 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{bunion{'A; 'B}} }

(*
 * Formation.
 *)
interactive bunionFormation 'H :
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * Membership.
 *)
interactive bunionMemberEqualityLeft 'H :
   sequent [squash] { 'H >- 'x = 'y in 'A } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- 'x = 'y in bunion{'A; 'B} }

interactive bunionMemberEqualityRight 'H :
   sequent [squash] { 'H >- 'x = 'y in 'B } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- 'x = 'y in bunion{'A; 'B} }

(*
 * Elimination.
 *)
interactive bunionElimination 'H 'J 'y 'z :
   sequent ['ext] { 'H; x: bunion{'A; 'B}; 'J['x]; y: 'A; z: 'y = 'x in bunion{'A; 'B} >- 'C['x] } -->
   sequent ['ext] { 'H; x: bunion{'A; 'B}; 'J['x]; y: 'B; z: 'y = 'x in bunion{'A; 'B} >- 'C['x] } -->
   sequent ['ext] { 'H; x: bunion{'A; 'B}; 'J['x] >- 'C['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D tactic.
 *)
let d_bunionT i p =
   if i = 0 then
      raise (RefineError ("d_bunion", StringError "no introduction rule"))
   else
      let j, k = Sequent.hyp_indices p i in
      let u, v = maybe_new_vars2 p "u" "v" in
         bunionElimination j k u v p

let bunion_term = << bunion{'A; 'B} >>

let d_resource = Mp_resource.improve d_resource (bunion_term, d_bunionT)

let d_bunion_typeT i p =
   if i = 0 then
      (bunionType (Sequent.hyp_count_addr p)
       thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_bunion_type", StringError "no elimination form"))

(*
 * EQCD.
 *)
let eqcd_bunionT p =
   (bunionEquality (Sequent.hyp_count_addr p)
    thenT addHiddenLabelT "wf") p

let eqcd_resource = Mp_resource.improve eqcd_resource (bunion_term, eqcd_bunionT)

let bunion_equal_term = << bunion{'A1; 'B1} = bunion{'A2; 'B2} in univ[@i:l] >>

let d_resource = Mp_resource.improve d_resource (bunion_equal_term, d_wrap_eqcd eqcd_bunionT)

let d_bunion_memberT i p =
   if i = 0 then
      let sel = get_sel_arg p in
      let tac =
         if sel = 1 then
            bunionMemberEqualityLeft
         else
            bunionMemberEqualityRight
      in
         (tac (Sequent.hyp_count_addr p)
          thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_bunion_memberT", StringError "no elimination form"))

let bunion_member_term = << 'x = 'y in bunion{'A; 'B} >>

let d_resource = Mp_resource.improve d_resource (bunion_member_term, d_bunion_memberT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
