(*
 * Int is the type of tokens (strings)
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
 *
 *)

include Tacticals

include Itt_equal
include Itt_rfun
include Itt_logic

open Refiner.Refiner.Term

open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare int
declare natural_number[@n:n]
declare ind{'i; m, z. 'down; 'base; m, z. 'up}

val int_term : term
val zero : term

declare "add"{'a; 'b}
declare "sub"{'a; 'b}
declare "mul"{'a; 'b}
declare "div"{'a; 'b}
declare "rem"{'a; 'b}

(*
 * Propositions.
 *)
declare lt{'a; 'b}
declare le{'a; 'b}
declare ge{'a; 'b}
declare gt{'a; 'b}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_compare
prec prec_add
prec prec_mul

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfoldLE  : le{'a; 'b} <--> ('a < 'b or 'a = 'b in int)
rewrite unfoldGT  : gt{'a; 'b} <--> 'b < 'a
rewrite unfoldGE  : ge{'a; 'b} <--> ('b < 'a or 'a = 'b in int)

rewrite reduceAdd : "add"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i + @j]
rewrite reduceSub : "sub"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i - @j]
rewrite reduceMul : "mul"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i * @j]
rewrite reduceDiv : "div"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i / @j]
rewrite reduceRem : "rem"{natural_number[@i:n]; natural_number[@j:n]} <--> natural_number[@i % @j]

rewrite reduceLT : "lt"{natural_number[@i:n]; natural_number[@j:n]} <--> "prop"[@i < @j]
rewrite reduceEQ : (natural_number[@i:n] = natural_number[@j:n] in int) <--> "prop"[@i = @j]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Reduction on induction combinator:
 * Three cases:
 *    let ind[x] = ind(x; i, j. down[i, j]; base; k, l. up[k, l]
 *    x < 0 => (ind[x] -> down[x, ind[x + 1]]
 *    x = 0 => (ind[x] -> base)
 *    x > 0 => (ind[x] -> up[x, ind[x - 1]]
 *)
rewrite indReduceDown :
   'x < 0 -->
   ((ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) <-->
    'down['x; ind{('x +@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

rewrite indReduceUp :
   ('x > 0) -->
   (ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
    'up['x; ind{('x -@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

rewrite indReduceBase :
   (ind{0; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) <-->
   'base

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Z
 * by intFormation
 *)
rule intFormation 'H : sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- int Type
 *)
rule intType 'H : sequent ['ext] { 'H >- "type"{int} }

(*
 * H >- Z = Z in Ui ext Ax
 * by intEquality
 *)
rule intEquality 'H : sequent ['ext] { 'H >- int = int in univ[@i:l] }

(*
 * H >- Z ext n
 * by numberFormation n
 *)
rule numberFormation 'H natural_number[@n:n] : sequent ['ext] { 'H >- int }

(*
 * H >- i = i in int
 * by numberEquality
 *)
rule numberEquality 'H : sequent ['ext] { 'H >- natural_number[@n:n] = natural_number[@n:n] in int }

(*
 * Induction:
 * H, n:Z, J[n] >- C[n] ext ind(i; m, z. down[n, m, it, z]; base[n]; m, z. up[n, m, it, z])
 * by intElimination [m; v; z]
 *
 * H, n:Z, J[n], m:Z, v: m < 0, z: C[m + 1] >- C[m] ext down[n, m, v, z]
 * H, n:Z, J[n] >- C[0] ext base[n]
 * H, n:Z, J[n], m:Z, v: 0 < m, z: C[m - 1] >- C[m] ext up[n, m, v, z]
 *)
rule intElimination 'H 'J 'n 'm 'v 'z :
   sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 'm < 0; z: 'C['m add 1] >- 'C['m] } -->
   sequent ['ext] { 'H; n: int; 'J['n] >- 'C[0] } -->
   sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 0 < 'm; z: 'C['m sub 1] >- 'C['m] } -->
   sequent ['ext] { 'H; n: int; 'J['n] >- 'C['n] }

(*
 * Equality on induction combinator:
 * let a = ind(x1; i1, j1. down1[i1, j1]; base1; k1, l1. up1[k1, l1])
 * let b = ind(x2; i2, j2. down2[i2, j2]; base2; k2, l2. up2[k2, l2])
 *
 * H >- a = b in T[x1]
 * by indEquality [z. T[z]; x; y; w]
 *
 * H >- x1 = y1 in Z
 * H, x: Z, w: x < 0, y: T[x + 1] >- down1[x, y] = down2[x, y] in T[x]
 * H >- base1 = base2 in T[0]
 * H, x: Z, w: 0 < x, y: T[x - 1] >- up1[x, y] = up2[x, y] in T[x]
 *)
rule indEquality 'H lambda{z. 'T['z]} 'x 'y 'w :
   sequent [squash] { 'H >- 'x1 = 'x2 in int } -->
   sequent [squash] { 'H; x: int; w: 'x < 0; y: 'T['x add 1] >- 'down1['x; 'y] = 'down2['x; 'y] in 'T['x] } -->
   sequent [squash] { 'H >- 'base1 = 'base2 in 'T[0] } -->
   sequent [squash] { 'H; x: int; w: 'x > 0; y: 'T['x sub 1] >- 'up1['x; 'y] = 'up2['x; 'y] in 'T['x] } -->
   sequent ['ext] { 'H >- ind{'x1; i1, j1. 'down1['i1; 'j1]; 'base1; k1, l1. 'up1['k1; 'l1]}
                   = ind{'x2; i2, j2. 'down2['i2; 'j2]; 'base2; k2, l2. 'up2['k2; 'l2]}
                   in 'T['x1] }

(*
 * less_thanFormation:
 * H >- Ui ext a < b
 * by less_thanFormation
 *
 * H >- Z ext a
 * H >- Z ext b
 *)
rule less_thanFormation 'H :
   sequent ['ext] { 'H >- int } -->
   sequent ['ext] { 'H >- int } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- i1 < j1 = i2 < j2 in Ui
 * by less_thanEquality
 *
 * H >- i1 = j1 in int
 * H >- i2 = j2 in int
 *)
rule less_thanEquality 'H :
   sequent [squash] { 'H >- 'i1 = 'j1 in int } -->
   sequent [squash] { 'H >- 'i2 = 'j2 in int } -->
   sequent ['ext] { 'H >- 'i1 < 'j1 = 'i2 < 'j2 in univ[@i:l] }

(*
 * H >- it = it in (a < b)
 * by less_than_memberEquality
 *
 * H >- a < b
 *)
rule less_than_memberEquality 'H :
    sequent [squash] { 'H >- 'a < 'b } -->
    sequent ['ext] { 'H >- it = it in ('a < 'b) }

(*
 * H, x: a < b, J[x] >- C[x]
 * by less_than_Elimination i
 *
 * H, x: a < b; J[it] >- C[it]
 *)
rule less_thanElimination 'H 'J :
   sequent ['ext] { 'H; x: 'a < 'b; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: 'a < 'b; 'J['x] >- 'C['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval intSqequalT : tactic

val int_term : term
val is_int_term : term -> bool

val lt_term : term
val is_lt_term : term -> bool
val mk_lt_term : term -> term -> term
val dest_lt : term -> term * term

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

val add_term : term
val is_add_term : term -> bool
val mk_add_term : term -> term -> term
val dest_add : term -> term * term

val sub_term : term
val is_sub_term : term -> bool
val mk_sub_term : term -> term -> term
val dest_sub : term -> term * term

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

val natural_number_term : term
val is_natural_number_term : term -> bool
val dest_natural_number : term -> Mp_num.num
val mk_natural_number_term : Mp_num.num -> term

val ind_term : term
val is_ind_term : term -> bool
val dest_ind : term -> term * string * string * term * term * string * string * term
val mk_ind_term : term -> string -> string -> term -> term -> string -> string -> term -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
