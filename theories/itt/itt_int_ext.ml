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
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermType
open Refiner.Refiner.RefineError
open Rformat
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_meta
open Base_dtactic
open Base_auto_tactic

open Itt_equal
open Itt_struct
open Itt_squash
open Itt_int_base

let _ = show_loading "Loading Itt_int_ext%t"
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

let mul_term = << 'x *@ 'y >>
let mul_opname = opname_of_term mul_term
let is_mul_term = is_dep0_dep0_term mul_opname
let mk_mul_term = mk_dep0_dep0_term mul_opname
let dest_mul = dest_dep0_dep0_term mul_opname

let div_term = << 'x /@ 'y >>
let div_opname = opname_of_term div_term
let is_div_term = is_dep0_dep0_term div_opname
let mk_div_term = mk_dep0_dep0_term div_opname
let dest_div = dest_dep0_dep0_term div_opname

let rem_term = << "rem"{'x; 'y} >>
let rem_opname = opname_of_term rem_term
let is_rem_term = is_dep0_dep0_term rem_opname
let mk_rem_term = mk_dep0_dep0_term rem_opname
let dest_rem = dest_dep0_dep0_term rem_opname

let gt_term = << 'x > 'y >>
let gt_opname = opname_of_term gt_term
let is_gt_term = is_dep0_dep0_term gt_opname
let mk_gt_term = mk_dep0_dep0_term gt_opname
let dest_gt = dest_dep0_dep0_term gt_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_mul

dform mul_df1 : except_mode[src] :: parens :: "prec"[prec_mul] :: "mul"{'a; 'b} =
   slot["lt"]{'a} `" * " slot["le"]{'b}
dform mul_df2 : mode[src] :: parens :: "prec"[prec_mul] :: "mul"{'a; 'b} =
   slot["lt"]{'a} `" *@ " slot["le"]{'b}

dform div_df1 : except_mode[src] :: parens :: "prec"[prec_mul] :: "div"{'a; 'b} =
   slot["lt"]{'a} Nuprl_font!"div" slot["le"]{'b}
dform div_df2 : mode[src] :: parens :: "prec"[prec_mul] :: "div"{'a; 'b} =
   slot["lt"]{'a} `" /@ " slot["le"]{'b}

dform rem_df1 : except_mode[src] :: parens :: "prec"[prec_mul] :: "rem"{'a; 'b} =
   slot["lt"]{'a} `" % " slot["le"]{'b}
dform rem_df2 : mode[src] :: parens :: "prec"[prec_mul] :: "rem"{'a; 'b} =
   slot["lt"]{'a} `" %@ " slot["le"]{'b}

dform gt_df1 : parens :: "prec"[prec_compare] :: gt{'a; 'b} =
   slot["lt"]{'a} `" > " slot["le"]{'b}

define unfold_le :
   le{'a; 'b} <--> "assert"{le_bool{'a; 'b}}

define unfold_ge :
   ge{'a; 'b} <--> ('b <= 'a)

define unfold_neq_int :
   nequal{'a; 'b} <--> "assert"{bneq_int{'a; 'b}}

let le_term = << 'x <= 'y >>
let le_opname = opname_of_term le_term
let is_le_term = is_dep0_dep0_term le_opname
let mk_le_term = mk_dep0_dep0_term le_opname
let dest_le = dest_dep0_dep0_term le_opname

let ge_term = << 'x >= 'y >>
let ge_opname = opname_of_term ge_term
let is_ge_term = is_dep0_dep0_term ge_opname
let mk_ge_term = mk_dep0_dep0_term ge_opname
let dest_ge = dest_dep0_dep0_term ge_opname

let bneq_int_term = << bneq_int{'x; 'y} >>
let bneq_int_opname = opname_of_term bneq_int_term
let is_bneq_int_term = is_dep0_dep0_term bneq_int_opname
let mk_bneq_int_term = mk_dep0_dep0_term bneq_int_opname
let dest_bneq_int = dest_dep0_dep0_term bneq_int_opname

dform le_df1 : except_mode[src] :: parens :: "prec"[prec_compare] :: le{'a; 'b} =
   slot["lt"]{'a} Nuprl_font!le slot["le"]{'b}
dform le_df2 : mode[src] :: parens :: "prec"[prec_compare] :: le{'a; 'b} =
   slot["lt"]{'a} `" <= " slot["le"]{'b}

dform ge_df1 : except_mode[src] :: parens :: "prec"[prec_compare] :: ge{'a; 'b} =
   slot["lt"]{'a} Nuprl_font!ge slot["le"]{'b}
dform ge_df2 : mode[src] :: parens :: "prec"[prec_compare] :: ge{'a; 'b} =
   slot["lt"]{'a} `" >= " slot["le"]{'b}

dform bneq_int_df1 : parens :: "prec"[prec_compare] :: bneq_int{'a; 'b} =
   slot["lt"]{'a} `" " Nuprl_font!neq Nuprl_font!subb `" " slot["le"]{'b}

(*! @docoff *)



(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The binary arithmetic operators are defined using the
 * the @emph{meta} arithmetic operators that are @MetaPRL
 * builtin operations.
 * @end[doc]
 *)

prim_rw reduce_mul_meta : (number[i:n] *@ number[j:n]) <-->
   meta_prod{number[i:n]; number[j:n]}
prim_rw reduce_div_meta : (number[i:n] /@ number[j:n]) <-->
   meta_quot{number[i:n]; number[j:n]}
prim_rw reduce_rem_meta : "rem"{number[i:n]; number[j:n]} <-->
   meta_rem{number[i:n]; number[j:n]}

(*! @docoff *)

let reduce_mul =
   reduce_mul_meta thenC reduce_meta_prod

let reduce_div =
   reduce_div_meta thenC reduce_meta_quot

let reduce_rem =
   reduce_rem_meta thenC reduce_meta_rem

let resource reduce += [
   <<number[i:n] *@ number[j:n]>>, reduce_mul;
   <<number[i:n] /@ number[j:n]>>, reduce_div;
   <<"rem"{number[i:n]; number[j:n]}>>, reduce_rem;
]

(*!
 * @begin[doc]
 * @thysection{Well-formedness and algebraic properties of @tt[mul]}
 * @end[doc]
 *)
prim mul_wf {| intro []; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- 'a *@ 'b = 'a1 *@ 'b1 in int } = it

prim mul_Commut 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- ('a *@ 'b) ~ ('b *@ 'a) } = it

interactive_rw mul_Commut_rw :
   ('a IN int) -->
   ('b IN int) -->
   ('a *@ 'b) <--> ('b *@ 'a)

let mul_CommutC = mul_Commut_rw

prim mul_Assoc 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- ('a *@ ('b *@ 'c)) ~ (('a *@ 'b) *@ 'c) } = it

interactive_rw mul_Assoc_rw :
   ('a IN int) -->
   ('b IN int) -->
   ('c IN int) -->
   ('a *@ ('b *@ 'c)) <--> (('a *@ 'b) *@ 'c)

let mul_AssocC = mul_Assoc_rw

prim mul_add_Distrib 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- ('a *@ ('b +@ 'c)) ~ (('a *@ 'b) +@ ('a *@ 'c)) } = it

interactive_rw mul_add_Distrib_rw :
   ('a IN int) -->
   ('b IN int) -->
   ('c IN int) -->
   ('a *@ ('b +@ 'c)) <--> (('a *@ 'b) +@ ('a *@ 'c))

let mul_add_DistribC = mul_add_Distrib_rw

prim mul_Id 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   sequent ['ext] { 'H >- (1 *@ 'a) ~ 'a } = it

interactive_rw mul_Id_rw :
   ('a IN int) -->
   (1 *@ 'a) <--> 'a

let mul_IdC = mul_Id_rw

interactive mul_Id2 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   sequent ['ext] { 'H >- ('a *@ 1) ~ 'a }

interactive_rw mul_Id2_rw :
   ('a IN int) -->
   ('a *@ 1) <--> 'a

let mul_Id2C = mul_Id2_rw

prim mul_Zero 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   sequent ['ext] { 'H >- (0 *@ 'a) ~ 0 } = it

interactive_rw mul_Zero_rw :
   ('a IN int) -->
   (0 *@ 'a) <--> 0

let mul_ZeroC = mul_Zero_rw

interactive mul_Zero2 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   sequent ['ext] { 'H >- ('a *@ 0) ~ 0 }

interactive_rw mul_Zero2_rw :
   ('a IN int) -->
   ('a *@ 0) <--> 0

let mul_Zero2C = mul_Zero2_rw

interactive lt_mulPositMonoEq 'H 'c :
   sequent [squash] { 'H >- 0 < 'c } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} = lt_bool{('c *@ 'a); ('c *@ 'b) } in bool }

interactive lt_mulPositMono 'H 'c :
   sequent [squash] { 'H >- 0 < 'c } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} ~ lt_bool{('c *@ 'a); ('c *@ 'b) } }

interactive_rw lt_mulPositMono_rw 'c :
   (0 < 'c) -->
   ('a IN int) -->
   ('b IN int) -->
   ('c IN int) -->
   lt_bool{'a; 'b} <--> lt_bool{('c *@ 'a); ('c *@ 'b) }

let lt_mulPositMonoC = lt_mulPositMono_rw

interactive mul_uni_Assoc 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- ('a *@ (- 'b)) ~ ((- 'a) *@ 'b) }

interactive_rw mul_uni_Assoc_rw :
   ('a IN int) -->
   ('b IN int) -->
   ('a *@ (- 'b)) <--> ((- 'a) *@ 'b)

let mul_uni_AssocC = mul_uni_Assoc_rw

interactive lt_mulNegMono 'H 'c :
   sequent [squash] { 'H >- 'c < 0 } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} ~ lt_bool{('c *@ 'b) ; ('c *@ 'a)} }

interactive_rw lt_mulNegMono_rw 'c :
   ('c < 0)  -->
   ('a IN int) -->
   ('b IN int) -->
   ('c IN int) -->
   lt_bool{'a; 'b} <--> lt_bool{('c *@ 'b) ; ('c *@ 'a)}

let lt_mulNegMonoC = lt_mulNegMono_rw

(*!
 * @begin[doc]
 * @thysection{@tt[rem] definition and well-formedness}
 * @end[doc]
 *)
prim rem_baseReduce 'H :
   sequent [squash] { 'H >- 0 <= 'a } -->
   sequent [squash] { 'H >- 'a < 'b } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- ('a %@ 'b) ~ 'a } = it

interactive_rw rem_baseReduce_rw :
   (0 <= 'a) -->
   ('a < 'b) -->
   ('a IN int) -->
   ('b IN int) -->
   ('a %@ 'b) <--> 'a

let rem_baseReduceC = rem_baseReduce_rw

prim rem_indReduce 'H :
   sequent [squash] { 'H >- 0 < 'b } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- ((('a *@ 'b) +@ 'c) %@ 'b) ~ ('c %@ 'b) } = it

interactive_rw rem_indReduce_rw :
   (0 < 'b) -->
   ('a IN int) -->
   ('b IN int) -->
   ('c IN int) -->
   ((('a *@ 'b) +@ 'c) %@ 'b) <--> ('c %@ 'b)

let rem_indReduceC = rem_indReduce_rw

interactive rem_wf {| intro []; eqcd |} 'H :
   sequent [squash] { 'H >- "nequal"{'b ; 0} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- ('a %@ 'b) IN int }

(*!
 * @begin[doc]
 * @thysection{@tt[div] definition and properties}
 * @end[doc]
 *)
prim div_baseReduce 'H :
   sequent [squash] { 'H >- 0 <= 'a } -->
   sequent [squash] { 'H >- 'a < 'b } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- ('a /@ 'b) ~ 0 } = it

interactive_rw div_baseReduce_rw :
   (0 <= 'a) -->
   ('a < 'b) -->
   ('a IN int) -->
   ('b IN int) -->
   ('a /@ 'b) <--> 0

let div_baseReduceC = div_baseReduce_rw

prim div_indReduce 'H :
   sequent [squash] { 'H >- 0 < 'b } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- ((('a *@ 'b) +@ 'c) /@ 'b) ~ ('a +@ ('c /@ 'b)) } = it

interactive_rw div_indReduce_rw :
   (0 < 'b) -->
   ('a IN int) -->
   ('b IN int) -->
   ('c IN int) -->
   ((('a *@ 'b) +@ 'c) /@ 'b) <--> ('a +@ ('c /@ 'b))

let div_indReduceC = div_indReduce_rw

interactive div_wf {| intro []; eqcd |} 'H :
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

interactive add_divReduce 'H :
   sequent [squash] {'H >- 0 < 'a } -->
   sequent [squash] {'H >- 0 < 'b } -->
   sequent [squash] {'H >- 0 < 'c } -->
   [wf] sequent [squash] {'H >- 'a IN int } -->
   [wf] sequent [squash] {'H >- 'b IN int } -->
   [wf] sequent [squash] {'H >- 'c IN int } -->
   sequent ['ext] {'H >- ('a /@ 'c) +@ ('b /@ 'c) <= ('a +@ 'b) /@ 'c }

interactive div_Assoc 'H :
   sequent [squash] { 'H >- 0 <= 'a } -->
   sequent [squash] { 'H >- 0 < 'b } -->
   sequent [squash] { 'H >- 0 < 'c } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- (('a /@ 'b) /@ 'c) ~ ('a /@ ('b *@ 'c)) }

interactive_rw div_Assoc_rw :
   (0 <= 'a) -->
   (0 < 'b) -->
   (0 < 'c) -->
   ('a IN int) -->
   ('b IN int) -->
   ('c IN int) -->
   (('a /@ 'b) /@ 'c) <--> ('a /@ ('b *@ 'c))

let div_AssocC = div_Assoc_rw

interactive gt_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- "type"{gt{'a; 'b}} }

interactive le_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- "type"{le{'a; 'b}} }

interactive ge_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- "type"{ge{'a; 'b}} }

interactive ge_sqstable {| squash; intro [] |} 'H :
   sequent [squash] { 'H >- 'a >= 'b } -->
   sequent ['ext] { 'H >- it IN ('a >= 'b) }

(*
Incorrect but there has to be some assoc/commut/composition property

rewrite rem_Assoc 'H :
   sequent [squash] { 'H >- 0 <= 'a } -->
   sequent [squash] { 'H >- 0 < 'b } -->
   sequent [squash] { 'H >- 0 < 'c } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- ('a %@ 'b) %@ 'c <--> ('a %@ 'c) %@ 'b }

*)

(*
let resource reduce +=
   [<< ('a *@ ('b *@ 'c)) >>, mul_Assoc;
    << ('a *@ ('b +@ 'c)) >>, mul_add_Distrib;
    << (1 *@ 'a) >>, mul_Id;
    << ('a *@ 1) >>, mul_Id2;
    << (0 *@ 'a) >>, mul_Zero;
    << ('a *@ 0) >>, mul_Zero2;
    << ('a *@ (- 'b)) >>, mul_uni_Assoc]
*)

