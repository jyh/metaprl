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

open Mp_debug
open Mp_resource
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_meta
open Base_dtactic

open Itt_equal
open Itt_logic
open Itt_bool

let _ = show_loading "Loading Itt_int_bool%t"

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

dform eq_int_df : parens :: "prec"[prec_implies] :: except_mode[src] :: eq_int{'i; 'j} =
   slot{'i} " " `"=" " " slot{'j}

dform lt_int_df : parens :: "prec"[prec_implies] :: lt_int{'i; 'j} =
   slot{'i} " " `"<" " " slot{'j}

dform le_int_df : parens :: "prec"[prec_implies] :: except_mode[src] :: le_int{'i; 'j} =
   slot{'i} " " Nuprl_font!le " " slot{'j}

dform gt_int_df : parens :: "prec"[prec_implies] :: gt_int{'i; 'j} =
   slot{'i} " " `">" " " slot{'j}

dform ge_int_df : parens :: "prec"[prec_implies] :: except_mode[src] :: ge_int{'i; 'j} =
   slot{'i} " " Nuprl_font!ge " " slot{'j}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw reduce_eq_int' : eq_int{number[i:n]; number[j:n]} <-->
   meta_eq{number[i:n]; number[j:n]; btrue; bfalse}
prim_rw reduce_lt_int' : lt_int{number[i:n]; number[j:n]} <-->
   meta_lt{number[i:n]; number[j:n]; btrue; bfalse}
prim_rw reduce_gt_int' : gt_int{number[i:n]; number[j:n]} <-->
   meta_lt{number[j:n]; number[i:n]; btrue; bfalse}
prim_rw reduce_le_int : le_int{'i; 'j} <-->
   bor{eq_int{'i; 'j}; lt_int{'i; 'j}}
prim_rw reduce_ge_int : ge_int{'i; 'j} <-->
   bor{eq_int{'i; 'j}; gt_int{'i; 'j}}

let reduce_eq_int =
   reduce_eq_int' thenC reduce_meta_eq

let reduce_lt_int =
   reduce_lt_int' thenC reduce_meta_lt

let reduce_gt_int =
   reduce_gt_int' thenC reduce_meta_lt

let resource reduce +=
   [<< eq_int{number[i:n]; number[j:n]} >>, reduce_eq_int;
    << lt_int{number[i:n]; number[j:n]} >>, reduce_lt_int;
    << gt_int{number[i:n]; number[j:n]} >>, reduce_gt_int;
    << le_int{'i; 'j} >>, reduce_le_int;
    << ge_int{'i; 'j} >>, reduce_ge_int]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim eq_int_wf {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'i IN int } -->
   [wf] sequent [squash] { 'H >- 'j IN int } -->
   sequent ['ext] { 'H >- eq_int{'i; 'j} IN bool } =
   it

prim eq_int_assert_intro {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'x = 'y in int } -->
   sequent ['ext] { 'H >- "assert"{eq_int{'x; 'y}} } =
   it

prim eq_int_assert_elim {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; x: 'a = 'b in int; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{eq_int{'a; 'b}}; 'J['x] >- 'C['x] } =
   it

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
