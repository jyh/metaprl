(*
 * Some more about integers
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
 * Author: Yegor Bryukhov
 * ynb@mail.ru
 *
 *)

include Itt_equal
include Itt_rfun
include Itt_logic
include Itt_bool
include Itt_int_base

open Refiner.Refiner.Term

open Tactic_type.Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "mul"{'a; 'b}
declare "div"{'a; 'b}
declare "rem"{'a; 'b}

(*
 Definitions of >b <=b >=b
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
   gt{'a; 'b} <--> 'b < 'a

(*
Switching to define-version to provide the same behaviour as bool-relations,
i.d. rewritability of <= in the same extent as of <

rewrite unfold_le 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a <= 'b <--> ('a < 'b) \/ ('a = 'b in int) }

rewrite unfold_ge 'H :
   [wf] sequent [squash] { 'H >- a IN int } -->
   [wf] sequent [squash] { 'H >- b IN int } -->
   sequent ['ext] { 'H >- 'a >= 'b <--> ('a < 'b) \/ ('a = 'b in int) }
*)

define unfold_le :
   le{'a; 'b} <--> "assert"{le_bool{'a; 'b}}

define unfold_ge :
   ge{'a; 'b} <--> 'b <= 'a

define unfold_neq_int :
   nequal{'a; 'b} <--> "assert"{bneq_int{'a; 'b}}

rule mul_wf 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- 'a *@ 'b = 'a1 *@ 'b1 in int }

rewrite lt_mulPositMono 'H 'c:
   (0 < 'c ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('c *@ 'a); ('c *@ 'b) }

rewrite mul_Commut 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('a *@ 'b) <--> ('b *@ 'a)

rewrite mul_Assoc 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ('a *@ ('b *@ 'c)) <--> (('a *@ 'b) *@ 'c) 

rewrite mul_add_Distrib 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ('a *@ ('b +@ 'c)) <--> (('a *@ 'b) +@ ('a *@ 'c)) 

rewrite mul_Id 'H :
   ('a IN int ) -->
   'a <--> (1 *@ 'a) 

rewrite mul_Zero 'H :
   ('a IN int ) -->
   (0 *@ 'a) <--> 0
 
rewrite mul_uni_Assoc 'H :
   ('a IN int ) -->
   ('b IN int ) -->
   ('a *@ uni_minus{ 'b }) <--> (uni_minus{ 'a } *@ 'b)

rewrite lt_mulNegMono 'H 'c:
   ('c < 0 ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('c *@ 'b) ; ('c *@ 'a)} 

rewrite rem_baseReduce 'H:
   (0 <= 'a ) -->
   ('a < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('a rem 'b) <--> 'a 

rewrite rem_indReduce 'H:
   (0 < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ((('a *@ 'b) +@ 'c) rem 'b) <--> ('c rem 'b) 

rule rem_wf 'H :
   sequent [squash] { 'H >- "nequal"{'b ; 0} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- ('a rem 'b) IN int }

rewrite div_baseReduce 'H:
   (0 <= 'a ) -->
   ('a < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('a /@ 'b) <--> 0

rewrite div_indReduce 'H:
   (0 < 'b ) -->
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ((('a *@ 'b) +@ 'c) /@ 'b) <--> ('a +@ ('c /@ 'b)) 

rule div_wf 'H :
   sequent [squash] { 'H >- "nequal"{'b ; 0} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a /@ 'b IN int }

rule lt_divMono 'H 'b :
   sequent [squash] { 'H >- 0 < 'c } -->
   sequent [squash] { 'H >- 'a < 'b } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- 'a /@ 'c <= 'b /@ 'c }

rule add_divReduce 'H:
   sequent [squash] {'H >- 0 < 'a } -->
   sequent [squash] {'H >- 0 < 'b } -->
   sequent [squash] {'H >- 0 < 'c } -->
   [wf] sequent [squash] {'H >- 'a IN int } -->
   [wf] sequent [squash] {'H >- 'b IN int } -->
   [wf] sequent [squash] {'H >- 'c IN int } -->
   sequent ['ext] {'H >- ('a /@ 'c) +@ ('b /@ 'c) <= ('a +@ 'b) /@ 'c }

rewrite div_Assoc 'H:
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






