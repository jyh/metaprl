(*!
 * @spelling{gt_bool le_bool ge_bool gt le ge nequal mul div rem}
 *
 * @begin[doc]
 * @theory[Itt_int_ext]
 *
 * Some more about integers
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * Author: Yegor Bryukhov
 * @email{ynb@mail.ru}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Itt_equal
include Itt_rfun
include Itt_logic
include Itt_bool
include Itt_int_base
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Rformat
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_meta
open Base_dtactic

open Itt_equal
open Itt_struct
(************************************************************************
 * TERMS                                                                *
 ************************************************************************)
(*!
 * @begin[doc]
 * @terms
 * Multiplicative operations on int
 * @end[doc]
 *)
declare "mul"{'a; 'b}
declare "div"{'a; 'b}
declare "rem"{'a; 'b}

(*
 Definitions of >b <=b >=b
 *)

(*!
 * @begin[doc]
 * More order relation operations
 * @end[doc]
 *)
define unfold_gt_bool :
   gt_bool{'a; 'b} <--> lt_bool{'b; 'a}

define unfold_le_bool :
   le_bool{'a; 'b} <--> bnot{lt_bool{'b; 'a}}

define unfold_ge_bool :
   ge_bool{'a; 'b} <--> bnot{lt_bool{'a; 'b}}

define unfold_bneq_int :
   bneq_int{'a; 'b} <--> bnot{beq_int{'a; 'b}}

(*
 Prop-int-relations definitions
 *)

define unfold_gt :
   gt{'a; 'b} <--> ('b < 'a)

(*
Switching to define-version to provide the same behaviour as bool-relations,
i.d. rewritability of <= in the same extent as of <

prim_rw unfold_le :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a <= 'b <--> ('a < 'b) \/ ('a = 'b in int) }

prim_rw unfold_ge :
   [wf] sequent [squash] { 'H >- a IN int } -->
   [wf] sequent [squash] { 'H >- b IN int } -->
   sequent ['ext] { 'H >- 'a >= 'b <--> ('a < 'b) \/ ('a = 'b in int) }
*)

define unfold_le :
   le{'a; 'b} <--> "assert"{le_bool{'a; 'b}}

define unfold_ge :
   ge{'a; 'b} <--> ('b <= 'a)

define unfold_neq_int :
   nequal{'a; 'b} <--> "assert"{bneq_int{'a; 'b}}

(*! @docoff *)

(*!
 * @begin[doc]
 * @thysection{Well-formedness and algebraic properties of @tt[mul]}
 * @end[doc]
 *)
prim mul_wf {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- 'a *@ 'b = 'a1 *@ 'b1 in int } = it

interactive_rw lt_mulPositMono 'c:
   (0 < 'c ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('c *@ 'a); ('c *@ 'b) }

prim_rw mul_Commut :
   ('a IN int ) -->
   ('b IN int ) -->
   ('a *@ 'b) <--> ('b *@ 'a)

prim_rw mul_Assoc :
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ('a *@ ('b *@ 'c)) <--> (('a *@ 'b) *@ 'c) 

prim_rw mul_add_Distrib :
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ('a *@ ('b +@ 'c)) <--> (('a *@ 'b) +@ ('a *@ 'c)) 

prim_rw mul_Id :
   ('a IN int ) -->
   (1 *@ 'a) <--> 'a

prim_rw mul_Id2 :
   ('a IN int ) -->
   ('a *@ 1) <--> 'a

prim_rw mul_Zero :
   ('a IN int ) -->
   (0 *@ 'a) <--> 0
 
prim_rw mul_Zero2 :
   ('a IN int ) -->
   ('a *@ 0) <--> 0

interactive_rw mul_uni_Assoc :
   ('a IN int ) -->
   ('b IN int ) -->
   ('a *@ uni_minus{ 'b }) <--> (uni_minus{ 'a } *@ 'b)

interactive_rw lt_mulNegMono 'c:
   ('c < 0 ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('c *@ 'b) ; ('c *@ 'a)} 

(*!
 * @begin[doc]
 * @thysection{@tt[rem] definition and well-formedness}
 * @end[doc]
 *)
prim_rw rem_baseReduce :
   (0 <= 'a ) -->
   ('a < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('a rem 'b) <--> 'a 

prim_rw rem_indReduce :
   (0 < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ((('a *@ 'b) +@ 'c) rem 'b) <--> ('c rem 'b) 

interactive rem_wf {| intro_resource []; eqcd_resource |} 'H :
   sequent [squash] { 'H >- "nequal"{'b ; 0} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- ('a rem 'b) IN int }

(*!
 * @begin[doc]
 * @thysection{@tt[div] definition and properties}
 * @end[doc]
 *)
prim_rw div_baseReduce :
   (0 <= 'a ) -->
   ('a < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('a /@ 'b) <--> 0

prim_rw div_indReduce :
   (0 < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ((('a *@ 'b) +@ 'c) /@ 'b) <--> ('a +@ ('c /@ 'b)) 

interactive div_wf {| intro_resource []; eqcd_resource |} 'H :
   sequent [squash] { 'H >- "nequal"{'b ; 0} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a /@ 'b IN int }

interactive lt_divMono 'H 'b :
   sequent [squash] { 'H >- 0 < 'c } -->
   sequent [squash] { 'H >- 'a < 'b } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- 'a /@ 'c <= 'b /@ 'c }

interactive add_divReduce 'H:
   sequent [squash] {'H >- 0 < 'a } -->
   sequent [squash] {'H >- 0 < 'b } -->
   sequent [squash] {'H >- 0 < 'c } -->
   [wf] sequent [squash] {'H >- 'a IN int } -->
   [wf] sequent [squash] {'H >- 'b IN int } -->
   [wf] sequent [squash] {'H >- 'c IN int } -->
   sequent ['ext] {'H >- ('a /@ 'c) +@ ('b /@ 'c) <= ('a +@ 'b) /@ 'c }

interactive_rw div_Assoc :
   (0 <= 'a ) -->
   (0 < 'b ) -->
   (0 < 'c ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   (('a /@ 'b) /@ 'c) <--> ('a /@ ('b *@ 'c))

(*
Incorrect but there has to be some assoc/commut/composition property

rewrite rem_Assoc 'H:
   sequent [squash] { 'H >- 0 <= 'a } -->
   sequent [squash] { 'H >- 0 < 'b } -->
   sequent [squash] { 'H >- 0 < 'c } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- ('a rem 'b) rem 'c <--> ('a rem 'c) rem 'b }

*)


let reduce_info =
   [<< ('a *@ ('b *@ 'c)) >>, mul_Assoc;
    << ('a *@ ('b +@ 'c)) >>, mul_add_Distrib;
    << (1 *@ 'a) >>, mul_Id;
    << ('a *@ 1) >>, mul_Id2;
    << (0 *@ 'a) >>, mul_Zero;
    << ('a *@ 0) >>, mul_Zero2;
    << ('a *@ uni_minus{ 'b }) >>, mul_uni_Assoc]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info
