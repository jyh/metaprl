(*!
 * @spelling{int number ind add minus beq_int lt_bool}
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
include Itt_squash
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
open Tactic_type.Sequent

open Base_meta
open Base_auto_tactic
open Base_dtactic

open Itt_equal
open Itt_struct
open Itt_squash
open Itt_bool
open Itt_squiggle

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
declare minus{'a}

declare beq_int{'a; 'b}
declare lt_bool{'a; 'b}

(*!
 * @begin[doc]
 * Subtraction is composition of addition and unary minus
 *
 * @end[doc]
 *)
define unfold_sub :
   "sub"{'a ; 'b} <--> ('a +@ minus{'b})

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

let int_term = << int >>
let int_opname = opname_of_term int_term
let is_int_term = is_no_subterms_term int_opname

let beq_int_term = << beq_int{'x; 'y} >>
let beq_int_opname = opname_of_term beq_int_term
let is_beq_int_term = is_dep0_dep0_term beq_int_opname
let mk_beq_int_term = mk_dep0_dep0_term beq_int_opname
let dest_beq_int = dest_dep0_dep0_term beq_int_opname

let lt_term = << 'x < 'y >>
let lt_opname = opname_of_term lt_term
let is_lt_term = is_dep0_dep0_term lt_opname
let mk_lt_term = mk_dep0_dep0_term lt_opname
let dest_lt = dest_dep0_dep0_term lt_opname

let lt_bool_term = << lt_bool{'x; 'y} >>
let lt_bool_opname = opname_of_term lt_bool_term
let is_lt_bool_term = is_dep0_dep0_term lt_bool_opname
let mk_lt_bool_term = mk_dep0_dep0_term lt_bool_opname
let dest_lt_bool = dest_dep0_dep0_term lt_bool_opname

let add_term = << 'x +@ 'y >>
let add_opname = opname_of_term add_term
let is_add_term = is_dep0_dep0_term add_opname
let mk_add_term = mk_dep0_dep0_term add_opname
let dest_add = dest_dep0_dep0_term add_opname

let minus_term = <<minus{'a}>>
let minus_opname = opname_of_term minus_term
let is_minus_term = is_dep0_term minus_opname
let mk_minus_term = mk_dep0_term minus_opname
let dest_minus = dest_dep0_term minus_opname

let sub_term = << 'x -@ 'y >>
let sub_opname = opname_of_term sub_term
let is_sub_term = is_dep0_dep0_term sub_opname
let mk_sub_term = mk_dep0_dep0_term sub_opname
let dest_sub = dest_dep0_dep0_term sub_opname

let number_term = << number[n:n] >>
let number_opname = opname_of_term number_term
let is_number_term = is_number_term number_opname
let dest_number = dest_number_term number_opname
let mk_number_term = mk_number_term number_opname

let ind_term = << ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} >>
let ind_opname = opname_of_term ind_term
let is_ind_term = is_dep0_dep2_dep0_dep2_term ind_opname
let dest_ind = dest_dep0_dep2_dep0_dep2_term ind_opname
let mk_ind_term = mk_dep0_dep2_dep0_dep2_term ind_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_compare
prec prec_add
prec prec_unary
prec prec_unary < prec_add

(*
prec prec_mul < prec_apply
prec prec_add < prec_mul
prec prec_compare < prec_add
*)

dform int_prl_df : except_mode [src] :: int = mathbbZ
dform int_src_df : mode[src] :: int = `"int"

dform number_df : number[n:n] =
   slot[n:n]

dform beq_int_df1 : parens :: "prec"[prec_compare] :: beq_int{'a; 'b} =
   slot["lt"]{'a} `" =" Nuprl_font!subb `" " slot["le"]{'b}

dform add_df1 : except_mode[src] :: parens :: "prec"[prec_add] :: "add"{'a; 'b} =
   slot["le"]{'a} `" + " slot["lt"]{'b}
dform add_df2 : mode[src] :: parens :: "prec"[prec_add] :: "add"{'a; 'b} =
   slot["le"]{'a} `" +@ " slot["lt"]{'b}

dform minus_df1 : except_mode[src] :: parens :: "prec"[prec_unary] :: (- 'a) =
   `" - " slot["le"]{'a}
dform minus_df2 : mode[src] :: parens :: "prec"[prec_unary] :: (- 'a) =
   `" - " slot["le"]{'a}

dform sub_df1 : except_mode[src] :: parens :: "prec"[prec_add] :: "sub"{'a; 'b} =
   slot["lt"]{'a} `" - " slot["le"]{'b}
dform sub_df2 : mode[src] :: parens :: "prec"[prec_add] :: "sub"{'a; 'b} =
   slot["lt"]{'a} `" -@ " slot["le"]{'b}

dform lt_df1 : parens :: "prec"[prec_compare] :: lt{'a; 'b} =
   slot["lt"]{'a} `" < " slot["le"]{'b}

dform lt_bool_df1 : parens :: "prec"[prec_compare] :: lt_bool{'a; 'b} =
   slot["lt"]{'a} `" <" Nuprl_font!subb `" " slot["le"]{'b}

(*
 * Useful tactic to prove _rw from ~-rules
 *)
let sqFromRwT t =
   (fun p -> sqSubstT (Sequent.concl p) 0 p)
    thenMT
        autoT
    thenT t thenT trivialT

let testT p =
   let g =Sequent.goal p in
(*  let (g,_):(term * term list)=Refiner.Refiner.Refine.dest_msequent mseq in
   let es : Refiner.Refiner.TermMan.Term.esequent=Refiner.Refiner.TermMan.explode_sequent g in
   let (args,hyps,goals)=es in
   let gl = SEQ_SET.to_list goals in*)
   let (s2,h2)=Refiner.Refiner.TermMan.nth_hyp g 2 in
   begin
      print_term stdout g;
      printf "\nHL%sHL\n" s2;
      print_term stdout h2;
      print_term stdout (Refiner.Refiner.TermMan.nth_concl g 1);
(*      print_term_list stdout gl;*)
      failT p
   end

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

interactive_rw int_sqequal_rw 'b :
   ('a = 'b in int) -->
   'a <--> 'b

let int_sqequalC = int_sqequal_rw

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
prim_rw reduce_add : "add"{number[i:n]; number[j:n]} <-->
   meta_sum{number[i:n]; number[j:n]}

(*
prim_rw reduce_sub : "sub"{number[i:n]; number[j:n]} <-->
   meta_diff{number[i:n]; number[j:n]}
*)
prim_rw reduce_minus : minus{number[i:n]} <-->
   meta_diff{number[0:n]; number[i:n]}

prim_rw reduce_lt : "lt"{number[i:n]; number[j:n]} <-->
   meta_lt{number[i:n]; number[j:n]; btrue; bfalse}

(*
prim_rw reduce_eq : (number[i:n] = number[j:n] in int) <-->
   meta_eq{number[i:n]; number[j:n]}
*)

(*! @docoff *)

let reduce_add =
   reduce_add andthenC reduce_meta_sum

(*
let reduce_sub =
   reduce_sub andthenC reduce_meta_diff
*)
let reduce_minus =
   reduce_minus andthenC reduce_meta_diff

let reduce_lt =
   reduce_lt andthenC reduce_meta_lt

(*
let reduce_eq =
   reduce_eq andthenC reduce_meta_eq
*)

prim add_wf {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- 'a +@ 'b = 'a1 +@ 'b1 in int } = it

prim minus_wf {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   sequent ['ext] { 'H >- (-'a) = (-'a1) in int } = it

interactive sub_wf {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a = 'a1 in int } -->
   [wf] sequent [squash] { 'H >- 'b = 'b1 in int } -->
   sequent ['ext] { 'H >- 'a -@ 'b = 'a1 -@ 'b1 in int }

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

interactive lt_squashStable {| squash_resource |} 'H :
   sequent [squash] { 'H >- 'a < 'b } -->
   sequent ['ext] { 'H >- it IN ('a < 'b) }

interactive lt_wf {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- "type"{lt{'a; 'b}} }

(*!
 * @begin[doc]
 * @thysubsection{@tt{beq_int} and @tt{= in int} correspondence}
 *
 * @end[doc]
 *)
prim beq_int2prop 'H :
   [main] sequent [squash] { 'H >- "assert"{beq_int{'a; 'b}} } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'a = 'b in int } = it

(* Derived from previous *)
interactive eq_int_assert_elim {| elim_resource [ThinOption thinT] |} 'H 'J 'y:
   [main]sequent['ext]{ 'H; x:"assert"{beq_int{'a;'b}}; 'J[it];
                            y: 'a = 'b in int >- 'C[it]} -->
   [wf]sequent['ext]{ 'H; x:"assert"{beq_int{'a;'b}}; 'J[it] >- 'a IN int} -->
   [wf]sequent['ext]{ 'H; x:"assert"{beq_int{'a;'b}}; 'J[it] >- 'b IN int} -->
   sequent['ext]{ 'H; x:"assert"{beq_int{'a;'b}}; 'J['x] >- 'C['x]}

prim beq_int_is_true 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- beq_int{'a; 'b} ~ btrue } = it

interactive_rw beq_int_is_true_rw :
   ('a = 'b in int) -->
   beq_int{'a; 'b} <--> btrue

let beq_int_is_trueC = beq_int_is_true_rw

(*
 Derived from previous rewrite
 *)
interactive eq_2beq_int {| intro_resource [] |} 'H :
   sequent [squash] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- "assert"{beq_int{'a; 'b}} }

interactive lt_bool_member {| intro_resource [] |} 'H :
  [main]  sequent [squash] { 'H >- 'a < 'b } -->
(*  [wf] sequent [squash] { 'H >- 'a IN int } -->
  [wf] sequent [squash] { 'H >- 'b IN int } --> *)
  sequent ['ext] { 'H >- "assert"{lt_bool{'a; 'b}} }

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
   sequent [squash] { 'H; x: int; w: 'x < 0; y: 'T['x +@ 1] >- 'down1['x; 'y] = 'down2['x; 'y] in 'T['x] } -->
   sequent [squash] { 'H >- 'base1 = 'base2 in 'T[0] } -->
   sequent [squash] { 'H; x: int; w: 0 < 'x; y: 'T['x -@ 1] >- 'up1['x; 'y] = 'up2['x; 'y] in 'T['x] } -->
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

prim lt_Reflex 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} ~ bfalse } = it

interactive_rw lt_Reflex_rw :
   ( 'a IN int ) -->
   ( 'b IN int ) -->
   band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} <--> bfalse

let lt_ReflexC = lt_Reflex_rw

interactive lt_Asym 'H 'a 'b :
   [main] sequent [squash] { 'H >- 'a < 'b } -->
   [main] sequent [squash] { 'H >- 'b < 'a } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- 'C }

let lt_AsymT t1 t2 p =
      lt_Asym (Sequent.hyp_count_addr p) t1 t2 p

prim lt_Trichot 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext]
     { 'H >- bor{bor{lt_bool{'a; 'b};lt_bool{'b; 'a}}; beq_int{'a; 'b}} ~ btrue } = it

interactive_rw lt_Trichot_rw :
   ( 'a IN int ) -->
   ( 'b IN int ) -->
   bor{bor{lt_bool{'a; 'b};lt_bool{'b; 'a}}; beq_int{'a; 'b}} <--> btrue

let lt_TrichotC = lt_Trichot_rw

let splitIntC a b =
   foldC
      (mk_bor_term
         (mk_bor_term
            (mk_lt_bool_term a b)
            (mk_lt_bool_term b a))
         (mk_beq_int_term a b))
      lt_TrichotC

interactive splitInt 'H 'a 'b 'w :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [main] sequent ['ext] { 'H; w: ('a < 'b) >- 'C } -->
   [main] sequent ['ext] { 'H; w: 'a = 'b in int >- 'C } -->
   [main] sequent ['ext] { 'H; w: ('b < 'a) >- 'C } -->
   sequent ['ext] { 'H >- 'C }

let splitIntT t1 t2 p =
   let w = maybe_new_vars1 p "w" in
      splitInt (Sequent.hyp_count_addr p) t1 t2 w p

prim lt_Transit 'H 'b :
   [main] sequent [squash]
      { 'H >- band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'c} ~ btrue } = it

interactive_rw lt_Transit_rw 'b :
   ( band{lt_bool{'a; 'b};lt_bool{'b; 'c}} = btrue in bool ) -->
   ( 'a IN int ) -->
   ( 'b IN int ) -->
   ( 'c IN int ) -->
   lt_bool{'a; 'c} <--> btrue

let lt_TransitC = lt_Transit_rw

interactive ltDissect 'H 'b:
   [main] sequent [squash] { 'H >- 'a < 'b } -->
   [main] sequent [squash] { 'H >- 'b < 'c } -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- 'a < 'c }

let ltDissectT t1 p =
      ltDissect (Sequent.hyp_count_addr p) t1 p

prim lt_Discret 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} ~
                          bor{beq_int{('a +@ 1); 'b}; lt_bool{('a +@ 1); 'b}} } = it

interactive_rw lt_Discret_rw :
   ( 'a IN int ) -->
   ( 'b IN int ) -->
   lt_bool{'a; 'b} <--> bor{beq_int{('a +@ 1); 'b}; lt_bool{('a +@ 1); 'b}}

let lt_DiscretC = lt_Discret_rw

(*!
 * @begin[doc]
 *
 * Monotonicity:
 *
 * @end[doc]
 *)
prim lt_addMono 'H 'c :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- lt_bool{'a; 'b} ~ lt_bool{('a +@ 'c); ('b +@ 'c)} } = it

interactive_rw lt_addMono_rw 'c :
   ( 'a IN int ) -->
   ( 'b IN int ) -->
   ( 'c IN int ) -->
   lt_bool{'a; 'b} <--> lt_bool{('a +@ 'c); ('b +@ 'c)}

let lt_addMonoC = lt_addMono_rw

(*! @docoff *)

(*!
 * @begin[doc]
 * @thysubsection{Addition properties}
 *
 * @tt{add} is commutative and associative.
 *
 * @end[doc]
 *)
prim add_Commut 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- ('a +@ 'b) ~ ('b +@ 'a) } = it

interactive_rw add_Commut_rw :
   ( 'a IN int ) -->
   ( 'b IN int ) -->
   ('a +@ 'b) <--> ('b +@ 'a)

let add_CommutC = add_Commut_rw

interactive lt_add_lt 'H :
   [main] sequent [squash] { 'H >- 'a < 'b} -->
   [main] sequent [squash] { 'H >- 'c < 'd} -->
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   [wf] sequent [squash] { 'H >- 'd IN int } -->
   sequent ['ext] { 'H >- ('a +@ 'c) < ('b +@ 'd) }

let lt_add_ltT p =
      lt_add_lt (Sequent.hyp_count_addr p) p

prim add_Assoc 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- ('a +@ ('b +@ 'c)) ~ (('a +@ 'b) +@ 'c) } = it

interactive_rw add_Assoc_rw :
   ( 'a IN int ) -->
   ( 'b IN int ) -->
   ( 'c IN int ) -->
   ('a +@ ('b +@ 'c)) <--> (('a +@ 'b) +@ 'c)

let add_AssocC = add_Assoc_rw

interactive_rw add_Assoc2_rw :
   ( 'a IN int ) -->
   ( 'b IN int ) -->
   ( 'c IN int ) -->
   (('a +@ 'b) +@ 'c) <--> ('a +@ ('b +@ 'c))

let add_Assoc2C = add_Assoc2_rw

(*!
 * @begin[doc]
 *
 * 0 is neutral element for @tt{add} in @tt{int}
 *
 * @end[doc]
 *)
prim add_Id 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   sequent ['ext] { 'H >- ('a +@ 0) ~ 'a } = it

interactive_rw add_Id_rw :
   ( 'a IN int ) -->
   ('a +@ 0) <--> 'a

let add_IdC = add_Id_rw

interactive add_Id2 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   sequent ['ext] { 'H >- (0 +@ 'a) ~ 'a }

interactive_rw add_Id2_rw :
   ( 'a IN int ) -->
   (0 +@ 'a) <--> 'a

let add_Id2C = add_Id2_rw

(*!
 * @begin[doc]
 *
 * @tt{- 'a} is a inverse element for 'a in @tt{int}
 *
 * @end[doc]
 *)
prim minus_add_inverse 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   sequent ['ext] { 'H >- ( 'a +@ (- 'a ) ) ~ 0 } = it

interactive_rw minus_add_inverse_rw :
   ( 'a IN int ) -->
   ( 'a +@ (- 'a) ) <--> 0

let minus_add_inverseC = minus_add_inverse_rw
(*
let unfold_zeroC t = foldC (mk_add_term t (mk_minus_term t)) minus_add_inverseC

interactive minus_add_inverse2 'H :
   [wf] sequent [squash] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- 0 ~ ('c +@ (- 'c)) }
*)
(*
interactive add_Functionality 'H :
   [main] sequent ['ext] { 'H >- 'a ~ 'b } -->
   [wf] sequent ['ext] { 'H >- 'a IN int } -->
   [wf] sequent ['ext] { 'H >- 'b IN int } -->
   [wf] sequent ['ext] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- ('a +@ 'c) ~ ('b +@ 'c) }
*)
interactive add_Functionality 'H 'c :
   [main] sequent ['ext] { 'H >- ('a +@ 'c) ~ ('b +@ 'c) } -->
   [wf] sequent ['ext] { 'H >- 'a IN int } -->
   [wf] sequent ['ext] { 'H >- 'b IN int } -->
   [wf] sequent ['ext] { 'H >- 'c IN int } -->
   sequent ['ext] { 'H >- 'a ~ 'b }

interactive_rw add_Functionality_rw 'b 'c :
   (('a +@ 'c) ~ ('b +@ 'c)) -->
   ('a IN int) -->
   ('b IN int) -->
   ('c IN int) -->
   'a <--> 'b

let add_FunctionalityC = add_Functionality_rw

interactive minus_add_Distrib 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   [wf] sequent [squash] { 'H >- 'b IN int } -->
   sequent ['ext] { 'H >- (-('a +@ 'b)) ~ ((-'a) +@ (-'b)) }

interactive minus_minus_reduce 'H :
   [wf] sequent [squash] { 'H >- 'a IN int } -->
   sequent ['ext] { 'H >- (-(-'a)) ~ 'a }

(*! @docoff *)

(***********************************************************
 * TYPE INFERENCE
 ***********************************************************)

(*
 * Type of int.
 *)
let resource typeinf += (<<int>>, infer_univ1)

(*
 * Type of number.
 *)
let resource typeinf += (<<number[n:n]>>, Typeinf.infer_const <<int>>)

(*
let resource reduce +=
   [<< band{lt_bool{'a; 'b}; lt_bool{'b; 'a}} >>, lt_ReflexC;
    << ('a +@ 0) >>, add_IdC;
    << (0 +@ 'a) >>, add_Id2C;
    << ( 'a +@ (- 'a)) >>, minus_add_inverseC;
    << (-(-'a)) >>, minus_minus_reduceC;
    << ('a +@ ('b +@ 'c)) >>, add_AssocC]
*)
