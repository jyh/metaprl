(*
 * We define an equality on sets.
 * The normal intensional equality ('s1 = 's2 in set) is
 * not sufficient, because it is not a small type (it is in U2).
 *
 * We define and extensional equality by induction
 * on the sets.
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

include Czf_itt_pre_set

open Itt_equal

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Sequent
open Tacticals
open Var

open Base_auto_tactic

open Itt_equal
open Itt_rfun
open Itt_struct

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare eq_inner{'s1; 's2}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw reduce_eq_inner : eq_inner{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((all y1 : 'T1. exst y2: 'T2. eq_inner{.'f1['y1]; .'f2['y2]})
    & (all y2 : 'T2. exst y1: 'T1. eq_inner{.'f1['y1]; .'f2['y2]}))

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform eq_inner_df : mode[prl] :: eq_inner{'s1; 's2} =
   `"eq_inner(" slot {'s1} `"; " slot{'s2} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Membership in a universe.
 *)
interactive eq_inner_equality1 'H :
   sequent [squash] { 'H >- is_pre_set{'s1} } -->
   sequent [squash] { 'H >- is_pre_set{'s2} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} = eq_inner{'s1; 's2} in univ[1:l] }

(*
 * Membership in a universe.
 *)
interactive eq_inner_type 'H :
   sequent [squash] { 'H >- is_pre_set{'s1} } -->
   sequent [squash] { 'H >- is_pre_set{'s2} } -->
   sequent ['ext] { 'H >- "type"{eq_inner{'s1; 's2}} }

(*
 * More general equality in a universe.
 *)
interactive eq_inner_equality2 'H :
   sequent [squash] { 'H >- 's1 = 's3 in pre_set } -->
   sequent [squash] { 'H >- 's2 = 's4 in pre_set } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} = eq_inner{'s3; 's4} in univ[1:l] }

(*
 * Equivalence relation rules.
 *)
interactive eq_inner_ref 'H :
   sequent [squash] { 'H >- is_pre_set{'s1} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's1} }

interactive eq_inner_sym 'H :
   sequent [squash] { 'H >- is_pre_set{'s1} } -->
   sequent [squash] { 'H >- is_pre_set{'s2} } -->
   sequent ['ext] { 'H >- eq_inner{'s2; 's1} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} }

interactive eq_inner_trans 'H 's2 :
   sequent [squash] { 'H >- is_pre_set{'s1} } -->
   sequent [squash] { 'H >- is_pre_set{'s2} } -->
   sequent [squash] { 'H >- is_pre_set{'s3} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} } -->
   sequent ['ext] { 'H >- eq_inner{'s2; 's3} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's3} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Equality of inner equality.
 *)
let eqcd_eq_innerT p =
   let goal = Sequent.concl p in
   let _, eq1, eq2 = dest_equal goal in
   let j = hyp_count_addr p in
      if alpha_equal eq1 eq2 then
         eq_inner_equality1 j p
      else
         eq_inner_equality2 j p

let eq_inner_term = << eq_inner{'s1; 's2} >>

let eq_inner_equal_term = << eq_inner{'s1; 's2} = eq_inner{'s3; 's4} in univ[1:l] >>

let eqcd_resource = Mp_resource.improve eqcd_resource (eq_inner_term, eqcd_eq_innerT)

let d_resource = Mp_resource.improve d_resource (eq_inner_equal_term, d_wrap_eqcd eqcd_eq_innerT)

(*
 * Typehood.
 *)
let d_eq_inner_typeT i p =
   if i = 0 then
      eq_inner_type (hyp_count_addr p) p
   else
      raise (RefineError ("d_eq_inner_typeT", StringError "no elimination form"))

let eq_inner_type_term = << "type"{eq_inner{'s1; 's2}} >>

let d_resource = Mp_resource.improve d_resource (eq_inner_type_term, d_eq_inner_typeT)

(*
 * Equality relations.
 *)
let eqInnerRefT p =
   eq_inner_ref (hyp_count_addr p) p

let eqInnerSymT p =
   eq_inner_sym (hyp_count_addr p) p

let eqInnerTransT t p =
   eq_inner_trans (hyp_count_addr p) t p

(*
 * Always reasonable to try reflexivity.
 *)
let auto_resource =
   Mp_resource.improve auto_resource (**)
      { auto_name = "eqInnerRefT";
        auto_prec = trivial_prec;
        auto_tac = auto_wrap eqInnerRefT
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
