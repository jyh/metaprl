(*
 * Binary intersection.
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
open Tacticals

open Itt_equal

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare bisect{'A; 'B}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_bisect

dform bisect_df : mode[prl] :: parens :: "prec"[prec_bisect] :: bisect{'A; 'B} =
   slot["le"]{'A} `" " cap space slot{'B}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_bisect : bisect{'A; 'B} <-->
                          "isect"{bool; x. ifthenelse{'x; 'A; 'B}}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive bisectEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- bisect{'A1; 'B1} = bisect{'A2; 'B2} in univ[@i:l] }

interactive bisectType 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{bisect{'A; 'B}} }

(*
 * Formation.
 *)
interactive bisectFormation 'H :
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * Membership.
 *)
interactive bisectMemberEquality 'H :
   sequent [squash] { 'H >- 'x = 'y in 'A } -->
   sequent [squash] { 'H >- 'x = 'y in 'B } -->
   sequent ['ext] { 'H >- 'x = 'y in bisect{'A; 'B} }

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

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D tactic.
 *)
let d_bisectT i p =
   if i = 0 then
      raise (RefineError ("d_bisect", StringError "no introduction rule"))
   else
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

let d_resource = d_resource.resource_improve d_resource (bisect_term, d_bisectT)

let d_bisect_typeT i p =
   if i = 0 then
      (bisectType (Sequent.hyp_count_addr p)
       thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_bisect_type", StringError "no elimination form"))

let bisect_type_term = << "type"{bisect{'A; 'B}} >>

let d_resource = d_resource.resource_improve d_resource (bisect_type_term, d_bisect_typeT)

(*
 * EQCD.
 *)
let eqcd_bisectT p =
   (bisectEquality (Sequent.hyp_count_addr p)
    thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (bisect_term, eqcd_bisectT)

let bisect_equal_term = << bisect{'A1; 'B1} = bisect{'A2; 'B2} in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (bisect_equal_term, d_wrap_eqcd eqcd_bisectT)

let d_bisect_memberT i p =
   if i = 0 then
      (bisectMemberEquality (Sequent.hyp_count_addr p)
       thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_bisect_memberT", StringError "no elimination form"))

let bisect_member_term = << 'x = 'y in bisect{'A; 'B} >>

let d_resource = d_resource.resource_improve d_resource (bisect_member_term, d_bisect_memberT)

(*
 * Subtyping.
 *)
let d_bisect_aboveT i p =
   if i = 0 then
      let j = get_sel_arg p in
      let tac =
         if j = 1 then
            bisectSubtypeLeft
         else
            bisectSubtypeRight
      in
         (tac (Sequent.hyp_count_addr p)
          thenLT [addHiddenLabelT "wf";
                  idT]) p
   else
      raise (RefineError ("d_bisect_aboveT", StringError "no elimination form"))

let bisect_above_term = << subtype{bisect{'A; 'B}; 'C} >>

let d_resource = d_resource.resource_improve d_resource (bisect_above_term, d_bisect_aboveT)

let d_bisect_belowT i p =
   if i = 0 then
      bisectSubtypeBelow (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_bisect_belowT", StringError "no elimination form"))

let bisect_below_term = << subtype{'C; bisect{'A; 'B}} >>

let d_resource = d_resource.resource_improve d_resource (bisect_below_term, d_bisect_belowT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
