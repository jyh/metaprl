(*
 * Additional Boolean functions on integers.
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

include Itt_bool
include Itt_int
include Itt_logic

open Mp_resource
open Tacticals

open Itt_equal
open Itt_logic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Boolean valued predicates.
 *)
declare eq_int{'i; 'j}
declare lt_int{'i; 'j}
declare le_int{'i; 'j}
declare gt_int{'i; 'j}
declare ge_int{'i; 'j}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform eq_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: eq_int{'i; 'j} =
   slot{'i} " " `"=" " " slot{'j}

dform lt_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: lt_int{'i; 'j} =
   slot{'i} " " `"<" " " slot{'j}

dform le_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: le_int{'i; 'j} =
   slot{'i} " " Nuprl_font!le " " slot{'j}

dform gt_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: gt_int{'i; 'j} =
   slot{'i} " " `">" " " slot{'j}

dform ge_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: ge_int{'i; 'j} =
   slot{'i} " " Nuprl_font!ge " " slot{'j}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw reduceEQInt : eq_int{natural_number[@i:n]; natural_number[@j:n]} <--> bool_flag[@i = @j]
primrw reduceLTInt : lt_int{natural_number[@i:n]; natural_number[@j:n]} <--> bool_flag[@i < @j]
primrw reduceGTInt : gt_int{natural_number[@i:n]; natural_number[@j:n]} <--> bool_flag[@j < @i]
primrw reduceLEInt : le_int{'i; 'j} <--> bor{eq_int{'i; 'j}; lt_int{'i; 'j}}
primrw reduceGEInt : le_int{'i; 'j} <--> bor{eq_int{'i; 'j}; gt_int{'i; 'j}}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim eq_int_wf 'H :
   sequent [squash] { 'H >- member{int; 'i} } -->
   sequent [squash] { 'H >- member{int; 'j} } -->
   sequent ['ext] { 'H >- member{bool; eq_int{'i; 'j}} } =
   it

prim eq_int_assert_intro 'H :
   sequent [squash] { 'H >- 'x = 'y in int } -->
   sequent ['ext] { 'H >- "assert"{eq_int{'x; 'y}} } =
   it

prim eq_int_assert_elim 'H 'J :
   sequent ['ext] { 'H; x: 'a = 'b in int; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{eq_int{'a; 'b}}; 'J['x] >- 'C['x] } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Typehood.
 *)
let d_eq_int_wfT p =
   (eq_int_wf (Sequent.hyp_count_addr p)
    thenT addHiddenLabelT "wf") p

let eq_int_wf_term = << member{bool; eq_int{'i; 'j}} >>

let d_resource = d_resource.resource_improve d_resource (eq_int_wf_term, wrap_intro d_eq_int_wfT)

(*
 * Equality.
 *)
let d_eq_int_assertT i p =
   if i = 0 then
      eq_int_assert_intro (Sequent.hyp_count_addr p) p
   else
      let j, k = Sequent.hyp_indices p i in
         eq_int_assert_elim j k p

let eq_int_assert_term = << "assert"{eq_int{'v1; 'v2}} >>

let d_resource = d_resource.resource_improve d_resource (eq_int_assert_term, d_eq_int_assertT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
