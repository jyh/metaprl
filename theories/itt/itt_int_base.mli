(*
 *
 * The integers are formalized as a @emph{ruleitive}
 * type in the @Nuprl type theory.
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

include Itt_equal
include Itt_rfun
include Itt_bool
include Itt_logic

open Refiner.Refiner.Term

open Tactic_type.Tacticals
open Tactic_type.Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare int
declare number[n:n]
declare ind{'i; m, z. 'down; 'base; m, z. 'up}

declare "add"{'a; 'b}
declare minus{'a}

declare beq_int{'a; 'b}
declare lt_bool{'a; 'b}

define unfold_sub :
   "sub"{'a ; 'b} <--> ('a +@ (- 'b))

(*
 Prop-int-lt definition
 *)
define unfold_lt :
   lt{'a; 'b} <--> "assert"{lt_bool{'a; 'b}}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_compare
prec prec_add

(*
 * Useful tactic to prove _rw from ~-rules
 *)

topval finishSq2ExT : int -> tactic

topval sqeq2rwT : tactic -> tactic

(*
 * Integers are canonical.
 *)
rule int_sqequal 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- 'a ~ 'b }

topval int_sqequalC : term -> conv

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reduce_add : "add"{number[i:n]; number[j:n]} <-->
   meta_sum{number[i:n]; number[j:n]}
rewrite reduce_minus : ( - number[i:n]) <-->
   meta_diff{number[0:n]; number[i:n]}
(*
rewrite reduce_sub : "sub"{number[i:n]; number[j:n]} <-->
   meta_diff{number[i:n]; number[j:n]}
*)

(*
rewrite reduce_mul : "mul"{number[i:n]; number[j:n]} <-->
   meta_prod{number[i:n]; number[j:n]}
rewrite reduce_div : "div"{number[i:n]; number[j:n]} <-->
   meta_quot{number[i:n]; number[j:n]}
rewrite reduce_rem : "rem"{number[i:n]; number[j:n]} <-->
   meta_rem{number[i:n]; number[j:n]}
*)

rewrite reduce_lt : "lt"{number[i:n]; number[j:n]} <-->
   meta_lt{number[i:n]; number[j:n]}

(*
rewrite reduce_eq : (number[i:n] = number[j:n] in int) <-->
   meta_eq{number[i:n]; number[j:n]}
*)

val int_term : term
val is_int_term : term -> bool

val beq_int_term : term
val is_beq_int_term : term -> bool
val mk_beq_int_term : term -> term -> term
val dest_beq_int : term -> term * term

val lt_term : term
val is_lt_term : term -> bool
val mk_lt_term : term -> term -> term
val dest_lt : term -> term * term

val lt_bool_term : term
val is_lt_bool_term : term -> bool
val mk_lt_bool_term : term -> term -> term
val dest_lt_bool : term -> term * term

val add_term : term
val is_add_term : term -> bool
val mk_add_term : term -> term -> term
val dest_add : term -> term * term

val minus_term : term
val is_minus_term : term -> bool
val mk_minus_term : term -> term
val dest_minus : term -> term

val sub_term : term
val is_sub_term : term -> bool
val mk_sub_term : term -> term -> term
val dest_sub : term -> term * term

val number_term : term
val is_number_term : term -> bool
val dest_number : term -> Mp_num.num
val mk_number_term : Mp_num.num -> term

val ind_term : term
val is_ind_term : term -> bool
val dest_ind : term -> term * string * string * term * term * string * string * term
val mk_ind_term : term -> string -> string -> term -> term -> string -> string -> term -> term

rule add_wf 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- 'a +@ 'b = 'a1 +@ 'b1 in int }

rule minus_wf 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   sequent ['ext] { 'H >- (- 'a) = (- 'a1) in int }

rule lt_bool_wf 'H :
   sequent [squash] { 'H >- 'a='a1 in int } -->
   sequent [squash] { 'H >- 'b='b1 in int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} = lt_bool{'a1; 'b1} in bool }

(* Derived from previous *)
rule lt_bool_wf2 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} IN bool }

rule beq_wf 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- beq_int{'a; 'b} = beq_int{'a1; 'b1} in bool }

rule lt_squashElimination 'H :
   sequent [squash] { 'H >- 'a < 'b } -->
   sequent ['ext] { 'H >- 'a < 'b }

rule beq_int2prop 'H :
   [main] sequent [squash] { 'H >- "assert"{beq_int{'a; 'b}} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a = 'b in int }

(* Derived from previous *)
rule eq_int_assert_elim 'H 'J 'y :
   [main]sequent['ext]{ 'H; x:"assert"{beq_int{'a;'b}}; 'J[it];
                            y: 'a = 'b in int >- 'C[it]} -->
   [wf]sequent['ext]{ 'H; x:"assert"{beq_int{'a;'b}}; 'J[it] >- 'a IN int} -->
   [wf]sequent['ext]{ 'H; x:"assert"{beq_int{'a;'b}}; 'J[it] >- 'b IN int} -->
   sequent['ext]{ 'H; x:"assert"{beq_int{'a;'b}}; 'J['x] >- 'C['x]}

rule beq_int_is_true 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- beq_int{'a; 'b} ~ btrue }

topval beq_int_is_trueC: conv

(*
 Derived from previous rewrite
 *)
rule eq_2beq_int 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- "assert"{beq_int{'a; 'b}} }

(*
 * Reduction on induction combinator:
 * Three cases:
 *    let ind[x] = ind(x; i, j. down[i, j]; base; k, l. up[k, l]
 *    x < 0 => (ind[x] -> down[x, ind[x + 1]]
 *    x = 0 => (ind[x] -> base)
 *    x > 0 => (ind[x] -> up[x, ind[x - 1]]
 *)
rewrite reduce_ind_down :
   ('x < 0) -->
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
    ('down['x; ind{('x +@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

rewrite reduce_ind_up :
   (0 < 'x) -->
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
   ('up['x; ind{('x -@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

rewrite reduce_ind_base :
   (ind{0; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) <-->
   'base

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Z
 * by intFormation
 *)
rule intFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H >- int Type
 *)
rule intType 'H :
   sequent ['ext] { 'H >- "type"{int} }

(*
 * H >- Z = Z in Ui ext Ax
 * by intEquality
 *)
rule intEquality 'H :
   sequent ['ext] { 'H >- int = int in univ[i:l] }

(*
 * H >- Z ext n
 * by numberFormation n
 *)
rule numberFormation 'H number[n:n] :
   sequent ['ext] { 'H >- int }
(*
 * H >- i = i in int
 * by numberEquality
 *)
rule numberEquality 'H :
   sequent ['ext] { 'H >- number[n:n] = number[n:n] in int }

(*
 * Induction:
 * H, n:Z, J[n] >- C[n] ext ind(i; m, z. down[n, m, it, z]; base[n]; m, z.
up[n, m, it, z])
 * by intElimination [m; v; z]
 *
 * H, n:Z, J[n], m:Z, v: m < 0, z: C[m + 1] >- C[m] ext down[n, m, v, z]
 * H, n:Z, J[n] >- C[0] ext base[n]
 * H, n:Z, J[n], m:Z, v: 0 < m, z: C[m - 1] >- C[m] ext up[n, m, v, z]
 *)
rule intElimination 'H 'J 'n 'm 'v 'z :
   sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 'm < 0; z: 'C['m +@ 1] >- 'C['m] } -->
   sequent ['ext] { 'H; n: int; 'J['n] >- 'C[0] } -->
   sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 0 < 'm; z: 'C['m -@ 1] >- 'C['m] } -->
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
   sequent [squash] { 'H; x: int; w: 'x < 0; y: 'T['x +@ 1] >- 'down1['x; 'y] = 'down2['x; 'y] in 'T['x] } -->
   sequent [squash] { 'H >- 'base1 = 'base2 in 'T[0] } -->
   sequent [squash] { 'H; x: int; w: 0 < 'x; y: 'T['x -@ 1] >- 'up1['x; 'y] = 'up2['x; 'y] in 'T['x] } -->
   sequent ['ext] { 'H >- ind{'x1; i1, j1. 'down1['i1; 'j1]; 'base1; k1, l1. 'up1['k1; 'l1]}
                   = ind{'x2; i2, j2. 'down2['i2; 'j2]; 'base2; k2, l2. 'up2['k2; 'l2]}
                   in 'T['x1] }
(*
 Definition of basic operations (and relations) on int
 *)

rule lt_Reflex 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} ~ bfalse }

topval lt_ReflexC: conv

rule lt_Trichot 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext]
     { 'H >- bor{bor{lt_bool{'a; 'b};lt_bool{'b; 'a}}; beq_int{'a; 'b}} ~ btrue }

topval lt_TrichotC: conv

(*
Switching to rewrite to provide the uniform of int-properties

rule lt_Transit 'H 'b :
   sequent [squash] { 'H >- 'a < 'b } -->
   sequent [squash] { 'H >- 'b < 'c } -->
   sequent ['ext] { 'H >- 'a < 'c }
*)

rule lt_Transit 'H 'b :
   [main] sequent [squash]
   	{ 'H >- band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'c} ~ btrue }

topval lt_TransitC: term -> conv

rule lt_Discret 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} ~
                          bor{beq_int{('a +@ 1); 'b}; lt_bool{('a +@ 1); 'b}} }

topval lt_DiscretC: conv

rule lt_addMono 'H 'c:
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} ~ lt_bool{('a +@ 'c); ('b +@ 'c)} }

topval lt_addMonoC: term -> conv

rule add_Commut 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- ('a +@ 'b) ~ ('b +@ 'a) }

topval add_CommutC: conv

rule add_Assoc 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- ('a +@ ('b +@ 'c)) ~ (('a +@ 'b) +@ 'c) }

topval add_AssocC: conv
topval add_Assoc2C: conv

rule add_Id 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   sequent ['ext] { 'H >- ('a +@ 0) ~ 'a }

topval add_IdC: conv

rule add_Id2 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   sequent ['ext] { 'H >- (0 +@ 'a) ~ 'a }

topval add_Id2C: conv

rule minus_add_inverse 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   sequent ['ext] { 'H >- ( 'a +@ ( - 'a ) ) ~ 0 }

topval minus_add_inverseC: conv
(*
topval unfold_zeroC: term -> conv

rule minus_add_inverse2 'H :
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- 0 ~ ('c +@ ( - 'c )) }
*)
(*
rule add_Functionality 'H :
   [main] sequent ['ext] { 'H >- 'a ~ 'b } -->
   [wf] sequent ['ext] { 'H >- 'a IN int } -->
   [wf] sequent ['ext] { 'H >- 'b IN int } -->
   [wf] sequent ['ext] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- ('a +@ 'c) ~ ('b +@ 'c) }
*)
rule add_Functionality 'H 'c :
   [main] sequent ['ext] { 'H >- ('a +@ 'c) ~ ('b +@ 'c) } -->
   [wf] sequent ['ext] { 'H >- 'a IN int } -->
   [wf] sequent ['ext] { 'H >- 'b IN int } -->
   [wf] sequent ['ext] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- 'a ~ 'b }

topval add_FunctionalityC : term -> term -> conv

rule minus_add_Distrib 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- (- ('a +@ 'b)) ~ ( (- 'a) +@ (- 'b) ) }

rule minus_minus_reduce 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   sequent ['ext] { 'H >- (-(-'a)) ~ 'a }
