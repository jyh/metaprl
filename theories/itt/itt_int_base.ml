(*!
 * @spelling{int number ind add uni_minus beq_int lt_bool}
 *
 * @begin[doc]
 * @theory[Itt_int_base]
 *
 * The integers are formalized as a @emph{primitive}
 * type in the @Nuprl type theory.
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
include Itt_bool
include Itt_logic
include Itt_struct
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

let _ = show_loading "Loading Itt_int_base%t"
(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{int} term is the type of integers with elements
 * $$@ldots, @number{-2}, @number{-1}, @number{0}, @number{1}, @number{2}, @ldots$$
 *
 * The @tt{ind} term is the induction combinator for building
 * loops indexed by an integer argument.
 * @end[doc]
 *)
declare int
declare number[n:n]
declare ind{'i; m, z. 'down; 'base; m, z. 'up}

(*!
 * @begin[doc]
 * The basic arithmetic operators are defined with
 * the following terms. Basic predicates are boolean.
 * @end[doc]
 *)
declare "add"{'a; 'b}
declare uni_minus{'a}

declare beq_int{'a; 'b}
declare lt_bool{'a; 'b}

(*!
 * @begin[doc]
 * Subtraction is composition of addition and unary minus
 *
 * @end[doc]
 *)
define unfold_sub :
   "sub"{'a ; 'b} <--> ('a +@ uni_minus{'b})

(*!
 * @begin[doc]
 * Derived typed relations
 *
 * @end[doc]
 *)
(*
 Prop-int-lt definition
 *)
define unfold_lt :
   lt{'a; 'b} <--> "assert"{lt_bool{'a; 'b}}
(*! @docoff *)

(*!
 * @begin[doc]
 * @thysection{Rules and rewrites}
 * @thysubsection{Typehood and well-formedness of arithmetic operators}
 *
 * @end[doc]
 *)
(*
 * Integers are canonical.
 *)
prim int_sqequal 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- 'a ~ 'b } = it

prim add_wf {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- 'a +@ 'b = 'a1 +@ 'b1 in int } = it

prim uni_wf {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   sequent ['ext] { 'H >- uni_minus{'a} = uni_minus{'a1} in int } = it

prim lt_bool_wf {| intro_resource []; eqcd_resource |} 'H :
   sequent [squash] { 'H >- 'a='a1 in int } -->
   sequent [squash] { 'H >- 'b='b1 in int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} = lt_bool{'a1; 'b1} in bool } = it

(* Derived from previous *)
interactive lt_bool_wf2 {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} IN bool }

prim beq_wf {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- beq_int{'a; 'b} = beq_int{'a1; 'b1} in bool } = it
(*! @docoff *)

(*!
 * @begin[doc]
 * @thysubsection{@tt{beq_int} and @tt{= in int} correspondence}
 *
 * @end[doc]
 *)
prim beq_int2prop {| intro_resource []; eqcd_resource |} 'H :
   [main] sequent [squash] { 'H >- "assert"{beq_int{'a; 'b}} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a = 'b in int } = it

(* Derived from previous *)
interactive eq_int_assert_elim {| elim_resource [ThinOption thinT] |} 'H 'J :
   [main] sequent ['ext] { 'H; x: 'a = 'b in int; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{beq_int{'a; 'b}}; 'J['x] >- 'C['x] }

(*
rewrite beq_int_is_true 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- beq_int{'a; 'b} <--> "btrue" }
*)
prim_rw beq_int_is_true :
   ('a = 'b in int) -->
   beq_int{'a; 'b} <--> btrue

(*
 Derived from previous rewrite
 *)
interactive eq_2beq_int {| intro_resource [] |} 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- "assert"{beq_int{'a; 'b}} }

(*! @docoff *)

(*!
 * @begin[doc]
 * @thysubsection {@tt{ind} definition}
 * Reduction of the induction combinator @tt{ind} has three cases.
 * If the argument $x$ is $0$, the combinator reduces to the @i{base}
 * case; if it is positive, it reduces to the @i{up} case; and
 * if it is negative, it reduces to the @i{down} case.
 * The first argument in the @i{up} and @i{down} cases represents
 * the induction value, and the second argument represents the
 * ``next'' computational step.
 * @end[doc]
 *)

(*
 * Reduction on induction combinator:
 * Three cases:
 *    let ind[x] = ind(x; i, j. down[i, j]; base; k, l. up[k, l]
 *    x < 0 => (ind[x] -> down[x, ind[x + 1]]
 *    x = 0 => (ind[x] -> base)
 *    x > 0 => (ind[x] -> up[x, ind[x - 1]]
 *)
prim_rw reduce_ind_down :
   ('x < 0) -->
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
    ('down['x; ind{('x +@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

prim_rw reduce_ind_up :
   (0 < 'x) -->
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
   ('up['x; ind{('x -@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

prim_rw reduce_ind_base :
   (ind{0; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) <-->
   'base
(*! @docoff *)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @thysubsection{Typehood and well-formedness of @tt{int} and @tt{number}}
 *
 * The $@int$ type inhabits every universe, and it
 * is a type.
 * @end[doc]
 *)
(*
 * H >- Ui ext Z
 * by intFormation
 *)
prim intFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] } = int

(*
 * H >- int Type
 *)
prim intType {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "type"{int} } = it

(*
 * H >- Z = Z in Ui ext Ax
 * by intEquality
 *)
prim intEquality {| intro_resource []; eqcd_resource |} 'H :
   sequent ['ext] { 'H >- int = int in univ[i:l] } = it

(*
 * H >- Z ext n
 * by numberFormation n
 *)
prim numberFormation 'H number[n:n] :
   sequent ['ext] { 'H >- int } = number[n:n]
(*! @docoff *)

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * The $@int$ type contains the @hrefterm[number] terms.
 * @end[doc]
 *)
(*
 * H >- i = i in int
 * by numberEquality
 *)
prim numberEquality {| intro_resource []; eqcd_resource |} 'H :
   sequent ['ext] { 'H >- number[n:n] = number[n:n] in int } = it

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * Induction on an integer assumption produces three cases:
 * one for the base case $0$, one for induction on negative arguments,
 * and another for induction on positive arguments.  The proof extract term
 * uses the @tt{ind} term, which performs a case analysis on its argument.
 * @end[doc]
 *)
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
prim intElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'n 'm 'v 'z :
   ( 'down['n; 'm; 'v; 'z] : sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 'm < 0; z: 'C['m +@ 1] >- 'C['m] } ) -->
   ( 'base['n] : sequent ['ext] { 'H; n: int; 'J['n] >- 'C[0] } ) -->
   ( 'up['n; 'm; 'v; 'z] : sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 0 < 'm; z: 'C['m -@ 1] >- 'C['m] } ) -->
   sequent ['ext] { 'H; n: int; 'J['n] >- 'C['n] } =
      ind{'n; m, z. 'down['n; 'm; it; 'z]; 'base['n]; m, z. 'up['n; 'm; it; 'z]}

(*
 * @begin[doc]
 * @thysubsection{Combinator equality}
 *
 * Two @tt{ind} term compute values of type $T$ if each of the three
 * cases (zero, positive, and negative) produce values of type $T$.
 * @end[doc]
 *)
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
prim indEquality {| intro_resource []; eqcd_resource |} 'H lambda{z. 'T['z]} 'x 'y 'w :
   sequent [squash] { 'H >- 'x1 = 'x2 in int } -->
   sequent [squash] { 'H; x: int; w: 'x < 0; y: 'T['x add 1] >- 'down1['x; 'y] = 'down2['x; 'y] in 'T['x] } -->
   sequent [squash] { 'H >- 'base1 = 'base2 in 'T[0] } -->
   sequent [squash] { 'H; x: int; w: 0 < 'x; y: 'T['x sub 1] >- 'up1['x; 'y] = 'up2['x; 'y] in 'T['x] } -->
   sequent ['ext] { 'H >- ind{'x1; i1, j1. 'down1['i1; 'j1]; 'base1; k1, l1. 'up1['k1; 'l1]}
                   = ind{'x2; i2, j2. 'down2['i2; 'j2]; 'base2; k2, l2. 'up2['k2; 'l2]}
                   in 'T['x1] } =
   it
(*! @docoff *)


(*!
 * @begin[doc]
 * @thysubsection{Order relation properties}
 *
 * @tt{lt_bool} defines reflexive, decidable, transitive and 
 * discrete order on @tt{int}
 * @end[doc]
 *)
(*
 Definition of basic operations (and relations) on int
 *)

prim_rw lt_Reflex :
   ('a IN int) -->
   ('b IN int) -->
   band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} <--> bfalse

prim_rw lt_Trichot :
   ('a IN int ) -->
   ('b IN int ) -->
   bor{bor{lt_bool{'a; 'b};lt_bool{'b; 'a}}; beq_int{'a; 'b}} <--> btrue

(*
Switching to rewrite to provide the uniform of int-properties

rule lt_Transit 'H 'b:
   sequent [squash] { 'H >- 'a < 'b } -->
   sequent [squash] { 'H >- 'b < 'c } -->
   sequent ['ext] { 'H >- 'a < 'c }
*)

prim_rw lt_Transit 'b :
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   (band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool) -->
   lt_bool{'a; 'c} <--> btrue

prim_rw lt_Discret :
   ('a IN int ) -->
   ('b IN int ) -->
   lt_bool{'a; 'b} <--> bor{beq_int{('a +@ 1); 'b}; lt_bool{('a +@ 1); 'b}}

(*!
 * @begin[doc]
 *
 * Monotonicity:
 *
 * @end[doc]
 *)
prim_rw lt_addMono 'c:
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('a +@ 'c); ('b +@ 'c)}

(*! @docoff *)

(*!
 * @begin[doc]
 * @thysubsection{Addition properties}
 *
 * @tt{add} is commutative and associative.
 *
 * @end[doc]
 *)
prim_rw add_Commut :
   ('a IN int ) -->
   ('b IN int ) -->
   ('a +@ 'b) <--> ('b +@ 'a)

prim_rw add_Assoc :
   ('a IN int ) -->
   ('b IN int ) -->
   ('c IN int ) -->
   ('a +@ ('b +@ 'c)) <--> (('a +@ 'b) +@ 'c)

(*!
 * @begin[doc]
 *
 * 0 is neutral element for @tt{add} in @tt{int}
 *
 * @end[doc]
 *)
prim_rw add_Id :
   ('a IN int ) -->
   ('a +@ 0) <--> 'a

interactive_rw add_Id2 :
   ('a IN int ) -->
   (0 +@ 'a) <--> 'a

(*!
 * @begin[doc]
 *
 * @tt{uni_minus{'a}} is a inverse element for 'a in @tt{int}
 *
 * @end[doc]
 *)
prim_rw uni_add_inverse :
   ('a IN int ) -->
   ( 'a +@ uni_minus{ 'a } ) <--> 0 

interactive_rw uni_add_Distrib :
   ('a IN int ) -->
   ('b IN int ) -->
   uni_minus{ ('a +@ 'b) } <--> ( uni_minus{ 'b } +@ uni_minus{ 'b } ) 

interactive_rw uni_uni_reduce :
   ('a IN int ) -->
   uni_minus{ uni_minus{ 'a } } <--> 'a

(*! @docoff *)
(*
 * Type of int.
 *)
let typeinf_resource = Mp_resource.improve typeinf_resource (<<int>>, infer_univ1)

(*
 * Type of number.
 *)
let typeinf_resource =
   Mp_resource.improve typeinf_resource (<<number[n:n]>>, Typeinf.infer_const <<int>>)

let reduce_info =
   [<< band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} >>, lt_Reflex;
    << ('a +@ 0) >>, add_Id;
    << (0 +@ 'a) >>, add_Id2;
    << ( 'a +@ uni_minus{ 'a } ) >>, uni_add_inverse;
    << uni_minus{ uni_minus{ 'a } } >>, uni_uni_reduce;
    << ('a +@ ('b +@ 'c)) >>, add_Assoc]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info
