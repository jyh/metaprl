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
 * @email{ynb@mail.ru}
 *)

extends Itt_equal
extends Itt_rfun
extends Itt_logic
extends Itt_bool
extends Itt_int_base

open Refiner.Refiner.Term
open Tactic_type.Conversionals

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
   gt{'a; 'b} <--> ('b < 'a)

(*
Switching to define-version to provide the same behaviour as bool-relations,
i.d. rewritability of <= in the same extent as of <

rewrite unfold_le :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'a <= 'b <--> ('a < 'b) \/ ('a = 'b in int) }

rewrite unfold_ge :
   [wf] sequent { <H> >- a in int } -->
   [wf] sequent { <H> >- b in int } -->
   sequent { <H> >- 'a >= 'b <--> ('a < 'b) \/ ('a = 'b in int) }
*)

define unfold_le :
   le{'a; 'b} <--> "assert"{le_bool{'a; 'b}}

define unfold_ge :
   ge{'a; 'b} <--> ('b <= 'a)

define unfold_neq_int :
   nequal{'a; 'b} <--> "assert"{bneq_int{'a; 'b}}

define unfold_int_seg :
   int_seg{'i; 'j} <--> {x:int | 'x >= 'i & 'x < 'j}

define unfold_max: max{'i;'j} <--> if 'i<@ 'j then 'j else 'i

define unfold_min: min{'i;'j} <--> if 'i<@ 'j then 'i else 'j

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_mul

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

topval reduce_mul: conv
topval reduce_div: conv
topval reduce_rem: conv

val bneq_int_term : term
val is_bneq_int_term : term -> bool
val mk_bneq_int_term : term -> term -> term
val dest_bneq_int : term -> term * term

val le_term : term
val is_le_term : term -> bool
val mk_le_term : term -> term -> term
val dest_le : term -> term * term

val ge_term : term
val is_ge_term : term -> bool
val mk_ge_term : term -> term -> term
val dest_ge : term -> term * term

val gt_term : term
val is_gt_term : term -> bool
val mk_gt_term : term -> term -> term
val dest_gt : term -> term * term

val mul_term : term
val is_mul_term : term -> bool
val mk_mul_term : term -> term -> term
val dest_mul : term -> term * term

val div_term : term
val is_div_term : term -> bool
val mk_div_term : term -> term -> term
val dest_div : term -> term * term

val rem_term : term
val is_rem_term : term -> bool
val mk_rem_term : term -> term -> term
val dest_rem : term -> term * term

val neq_int_term : term
val is_neq_int_term : term -> bool
val mk_neq_int_term : term -> term -> term
val dest_neq_int : term -> term * term

rule ge_addWeakMono :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- ('a +@ 'c) >= ('b +@ 'c) }

rule ge_addWeakMono2 :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- ('c +@ 'a) >= ('c +@ 'b) }

rule ge_Transit 'b :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- 'b >= 'c } -->
   sequent { <H> >- 'a >= 'c }

rule ge_addMono :
   sequent { <H> >- 'a in int } -->
   sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'd in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- 'c >= 'd } -->
   sequent { <H> >- ('a +@ 'c) >= ('b +@ 'd) }

rule mul_wf :
   [wf] sequent { <H> >- 'a = 'a1 in int } -->
   [wf] sequent { <H> >- 'b = 'b1 in int } -->
   sequent { <H> >- 'a *@ 'b = 'a1 *@ 'b1 in int }

rule mul_Commut :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a *@ 'b) ~ ('b *@ 'a) }

topval mul_CommutC: conv

rule mul_Assoc :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a *@ ('b *@ 'c)) ~ (('a *@ 'b) *@ 'c) }

topval mul_AssocC: conv
topval mul_Assoc2C: conv

rule mul_add_Distrib :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a *@ ('b +@ 'c)) ~ (('a *@ 'b) +@ ('a *@ 'c)) }

topval mul_add_DistribC: conv

rewrite mul_add_Distrib2C :
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   (('a *@ 'b) +@ ('a *@ 'c)) <--> ('a *@ ('b +@ 'c))

rewrite mul_add_Distrib3C :
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   (('a +@ 'b) *@ 'c) <--> (('a *@ 'c) +@ ('b *@ 'c))

rule mul_Id :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- (1 *@ 'a) ~ 'a }

topval mul_IdC: conv
topval mul_Id2C: conv
topval mul_Id3C: conv

rule mul_Zero :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- (0 *@ 'a) ~ 0 }

rule lt_mulPositMonoEq 'c :
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{'a; 'b} = lt_bool{('c *@ 'a); ('c *@ 'b) } in bool }

rule lt_mulPositMono 'c :
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{'a; 'b} ~ lt_bool{('c *@ 'a); ('c *@ 'b) } }

rule mul_uni_Assoc :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a *@ (- 'b)) ~ ((- 'a) *@ 'b) }

topval mul_uni_AssocC : conv

rule lt_mulNegMono 'c :
   sequent { <H> >- 'c < 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{'a; 'b} ~ lt_bool{('c *@ 'b) ; ('c *@ 'a)} }

rule rem_baseReduce :
   sequent { <H> >- 0 <= 'a } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a %@ 'b) ~ 'a }

rule rem_indReduce :
   sequent { <H> >- 0 < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ((('a *@ 'b) +@ 'c) %@ 'b) ~ ('c %@ 'b) }

rule rem_wf :
   sequent { <H> >- "nequal"{'b ; 0} } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a %@ 'b) in int }

rule div_baseReduce :
   sequent { <H> >- 0 <= 'a } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a /@ 'b) ~ 0 }

rule div_indReduce :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ((('a *@ 'b) +@ 'c) /@ 'b) ~ ('a +@ ('c /@ 'b)) }

rule div_wf :
   sequent { <H> >- "nequal"{'b ; 0} } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'a /@ 'b in int }

rule lt_divMono 'b :
   sequent { <H> >- 0 < 'c } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a /@ 'c <= 'b /@ 'c }

rule add_divReduce :
   sequent { <H> >- 0 < 'a } -->
   sequent { <H> >- 0 < 'b } -->
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a /@ 'c) +@ ('b /@ 'c) <= ('a +@ 'b) /@ 'c }

rule div_Assoc :
   sequent { <H> >- 0 <= 'a } -->
   sequent { <H> >- 0 < 'b } -->
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- (('a /@ 'b) /@ 'c) ~ ('a /@ ('b *@ 'c)) }

topval fold_int_seg : conv
