(*!
 * @spelling{ge gt int le lt}
 *
 * @begin[doc]
 * @theory[Itt_int]
 *
 * The integers are formalized as a @emph{primitive}
 * type in the @Nuprl type theory.  Computation over the
 * integers is performed using primitive arithmetic
 * operations in the @MetaPRL prover.  This encoding is
 * fairly awkward; it is difficult to prove arithmetic
 * statements by referring to the primitive rules.  A
 * better solution would be to encode the integers using
 * the recursive type in the @hreftheory[Itt_srec] module.
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
 * Author: Jason Hickey
 * @email{jyh@cs.cornell.edu}
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

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_int%t"

(* debug_string DebugLoad "Loading itt_int..." *)

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
 * The binary arithmetic operators are defined with
 * the following terms.
 * The @tt{le}, @tt{gt}, and @tt{ge} binary operators
 * are defined in terms the integer order $<$ and equality.
 * @end[doc]
 *)
declare "add"{'a; 'b}
declare "sub"{'a; 'b}
declare "mul"{'a; 'b}
declare "div"{'a; 'b}
declare "rem"{'a; 'b}
declare lt{'a; 'b}
define unfold_le : le{'a; 'b} <--> (('a < 'b) or ('a = 'b in int))
define unfold_gt : gt{'a; 'b} <--> ('b < 'a)
define unfold_ge : ge{'a; 'b} <--> (('b < 'a) or ('a = 'b in int))
(*! @docoff *)


let int_term = << int >>
let int_opname = opname_of_term int_term
let is_int_term = is_no_subterms_term int_opname

let lt_term = << 'x < 'y >>
let lt_opname = opname_of_term lt_term
let is_lt_term = is_dep0_dep0_term lt_opname
let mk_lt_term = mk_dep0_dep0_term lt_opname
let dest_lt = dest_dep0_dep0_term lt_opname

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

let gt_term = << 'x > 'y >>
let gt_opname = opname_of_term gt_term
let is_gt_term = is_dep0_dep0_term gt_opname
let mk_gt_term = mk_dep0_dep0_term gt_opname
let dest_gt = dest_dep0_dep0_term gt_opname

let add_term = << 'x +@ 'y >>
let add_opname = opname_of_term add_term
let is_add_term = is_dep0_dep0_term add_opname
let mk_add_term = mk_dep0_dep0_term add_opname
let dest_add = dest_dep0_dep0_term add_opname

let sub_term = << 'x -@ 'y >>
let sub_opname = opname_of_term sub_term
let is_sub_term = is_dep0_dep0_term sub_opname
let mk_sub_term = mk_dep0_dep0_term sub_opname
let dest_sub = dest_dep0_dep0_term sub_opname

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
prec prec_mul

(*
prec prec_mul < prec_apply
prec prec_add < prec_mul
prec prec_compare < prec_add
*)

dform int_prl_df : except_mode [src] :: int = mathbbZ
dform int_src_df : mode[src] :: int = `"int"

dform number_df : number[n:n] =
   slot[n:n]

dform add_df1 : except_mode[src] :: parens :: "prec"[prec_add] :: "add"{'a; 'b} =
   slot["le"]{'a} `" + " slot["lt"]{'b}
dform add_df2 : mode[src] :: parens :: "prec"[prec_add] :: "add"{'a; 'b} =
   slot["le"]{'a} `" +@ " slot["lt"]{'b}

dform sub_df1 : except_mode[src] :: parens :: "prec"[prec_add] :: "sub"{'a; 'b} =
   slot["lt"]{'a} `" - " slot["le"]{'b}
dform sub_df2 : mode[src] :: parens :: "prec"[prec_add] :: "sub"{'a; 'b} =
   slot["lt"]{'a} `" -@ " slot["le"]{'b}

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

dform lt_df1 : parens :: "prec"[prec_compare] :: lt{'a; 'b} =
   slot["lt"]{'a} `" < " slot["le"]{'b}

dform le_df1 : except_mode[src] :: parens :: "prec"[prec_compare] :: le{'a; 'b} =
   slot["lt"]{'a} Nuprl_font!le slot["le"]{'b}
dform le_df2 : mode[src] :: parens :: "prec"[prec_compare] :: le{'a; 'b} =
   slot["lt"]{'a} `" <= " slot["le"]{'b}

dform ge_df1 : except_mode[src] :: parens :: "prec"[prec_compare] :: ge{'a; 'b} =
   slot["lt"]{'a} Nuprl_font!ge slot["le"]{'b}
dform ge_df2 : mode[src] :: parens :: "prec"[prec_compare] :: ge{'a; 'b} =
   slot["lt"]{'a} `" >= " slot["le"]{'b}

dform gt_df1 : parens :: "prec"[prec_compare] :: gt{'a; 'b} =
   slot["lt"]{'a} `" > " slot["le"]{'b}

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
prim_rw reduce_sub : "sub"{number[i:n]; number[j:n]} <-->
   meta_diff{number[i:n]; number[j:n]}
prim_rw reduce_mul : "mul"{number[i:n]; number[j:n]} <-->
   meta_prod{number[i:n]; number[j:n]}
prim_rw reduce_div : "div"{number[i:n]; number[j:n]} <-->
   meta_quot{number[i:n]; number[j:n]}
prim_rw reduce_rem : "rem"{number[i:n]; number[j:n]} <-->
   meta_rem{number[i:n]; number[j:n]}

prim_rw reduce_lt : "lt"{number[i:n]; number[j:n]} <-->
   meta_lt{number[i:n]; number[j:n]; btrue; bfalse}
prim_rw reduce_eq : (number[i:n] = number[j:n] in int) <-->
   meta_eq{number[i:n]; number[j:n]; btrue; bfalse}
(*! @docoff *)

let reduce_add =
   reduce_add thenC reduce_meta_sum

let reduce_sub =
   reduce_sub thenC reduce_meta_diff

let reduce_mul =
   reduce_mul thenC reduce_meta_prod

let reduce_div =
   reduce_div thenC reduce_meta_rem

let reduce_lt =
   reduce_lt thenC reduce_meta_lt

let reduce_eq =
   reduce_eq thenC reduce_meta_eq

(*!
 * @begin[doc]
 * Reduction of the induction combinator @tt{ind} has three cases.
 * If the argument $x$ is $0$, the combinator reduces to the @i{base}
 * case; if it is positive, it reduces to the @i{up} case; and
 * if it is negative, it reduces to the @i{down} case.
 * The first argument in the @i{up} and @i{down} cases represents
 * the induction value, and the second argument represents the
 * ``next'' computational step.
 * @end[doc]
 *)
prim_rw reduce_ind_down :
   ('x < 0) -->
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
   ('down['x; ind{('x +@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

prim_rw reduce_ind_up :
   ('x > 0) -->
   ind{'x; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} <-->
   ('up['x; ind{('x -@ 1); i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}])

prim_rw reduce_ind_base :
   (ind{0; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) <-->
   'base
(*! @docoff *)

ml_rw reduce_ind : ('goal : ind{number[x:n]; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]}) =
   let x, i, j, down, base, k, l, up = dest_ind goal in
   let x' = dest_number x in
   let code = Mp_num.compare_num x' (Mp_num.Int 0) in
      if code < 0 then
         let x'' = mk_number_term (Mp_num.succ_num x') in
         let goal = mk_ind_term x'' i j down base k l up in
            subst down [k; l] [x; goal]
      else if code > 0 then
         let x'' = mk_number_term (Mp_num.pred_num x') in
         let goal = mk_ind_term x'' i j down base k l up in
            subst up [k; l] [x; goal]
      else
         base


let resource reduce +=
   [<< "add"{number[i:n]; number[j:n]} >>, reduce_add;
    << "sub"{number[i:n]; number[j:n]} >>, reduce_sub;
    << "mul"{number[i:n]; number[j:n]} >>, reduce_mul;
    << "div"{number[i:n]; number[j:n]} >>, reduce_div;
    << "rem"{number[i:n]; number[j:n]} >>, reduce_rem;
    << ind{number[x:n]; i, j. 'down['i; 'j]; 'base; k, l. 'up['k; 'l]} >>, reduce_ind]

(************************************************************************
 * INTEGER RULES                                                        *
 ************************************************************************)

(*
 * H >- Ui ext Z
 * by intFormation
 *)
prim intFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] } = int

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Typehood and well-formedness}
 *
 * The $@int$ type inhabits every universe, and it
 * is a type.
 * @end[doc]
 *)
prim intType {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{int} } =
   it

(*
 * H >- Z = Z in Ui ext Ax
 * by intEquality
 *)
prim intEquality {| intro []; eqcd |} 'H :
   sequent ['ext] { 'H >- int IN univ[i:l] } =
   it
(*! @docoff *)

(*
 * H >- Z ext n
 * by numberFormation n
 *)
prim numberFormation 'H number[n:n] :
   sequent ['ext] { 'H >- int } =
   number[n:n]

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * The $@int$ type contains the @hrefterm[number] terms.
 * @end[doc]
 *)
prim numberEquality {| intro []; eqcd |} 'H :
   sequent ['ext] { 'H >- number[n:n] IN int } =
   it

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
prim intElimination {| elim [ThinOption thinT] |} 'H 'J 'n 'm 'v 'z :
   [main] ('down['n; 'm; 'v; 'z] : sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 'm < 0; z: 'C['m +@ 1] >- 'C['m] }) -->
   [main] ('base['n] : sequent ['ext] { 'H; n: int; 'J['n] >- 'C[0] }) -->
   [main] ('up['n; 'm; 'v; 'z] : sequent ['ext] { 'H; n: int; 'J['n]; m: int; v: 0 < 'm; z: 'C['m -@ 1] >- 'C['m] }) -->
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
prim indEquality {| intro []; eqcd |} 'H lambda{z. 'T['z]} 'x 'y 'w :
   [wf] sequent [squash] { 'H >- 'x1 = 'x2 in int } -->
   [wf] sequent [squash] { 'H; x: int; w: 'x < 0; y: 'T['x +@ 1] >- 'down1['x; 'y] = 'down2['x; 'y] in 'T['x] } -->
   [wf] sequent [squash] { 'H >- 'base1 = 'base2 in 'T[0] } -->
   [wf] sequent [squash] { 'H; x: int; w: 'x > 0; y: 'T['x -@ 1] >- 'up1['x; 'y] = 'up2['x; 'y] in 'T['x] } -->
   sequent ['ext] { 'H >- ind{'x1; i1, j1. 'down1['i1; 'j1]; 'base1; k1, l1. 'up1['k1; 'l1]}
                   = ind{'x2; i2, j2. 'down2['i2; 'j2]; 'base2; k2, l2. 'up2['k2; 'l2]}
                   in 'T['x1] } =
   it
(*! @docoff *)

(*
 * less_thanFormation:
 * H >- Ui ext a < b
 * by less_thanFormation
 *
 * H >- Z ext a
 * H >- Z ext b
 *)
prim less_thanFormation 'H :
   ('a : sequent ['ext] { 'H >- int }) -->
   ('b : sequent ['ext] { 'H >- int }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   'a < 'b

(*!
 * @begin[doc]
 * @thysubsection{Well-formedness of the arithmetic operators}
 *
 * The $<$ binary operator is a type if its arguments
 * are integers, and it is inhabited by the $@it$ term
 * if it is true.
 * @end[doc]
 *)
prim less_thanEquality {| intro []; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- 'i1 = 'j1 in int } -->
   [wf] sequent [squash] { 'H >- 'i2 = 'j2 in int } -->
   sequent ['ext] { 'H >- 'i1 < 'j1 = 'i2 < 'j2 in univ[i:l] } =
   it

(*
 * H >- it = it in (a < b)
 * by less_than_memberEquality
 *
 * H >- a < b
 *)
prim less_than_memberEquality {| intro []; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- 'a < 'b } -->
   sequent ['ext] { 'H >- it IN ('a < 'b) } =
   it
(*! @docoff *)

(*
 * H, x: a < b, J[x] >- C[x]
 * by less_than_Elimination i
 *
 * H, x: a < b; J[it] >- C[it]
 *)
prim less_thanElimination {| elim [ThinOption thinT] |} 'H 'J :
   ('t : sequent ['ext] { 'H; x: 'a < 'b; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: 'a < 'b; 'J['x] >- 'C['x] } =
   't

(*
 * Integers are canonical.
 *)
prim int_sqequal 'H :
   sequent [squash] { 'H >- 'i = 'j in int } -->
   sequent ['ext] { 'H >- 'i ~ 'j } =
   it

(*!
 * @begin[doc]
 * The well-formedness of the other binary operators
 * is derived by induction on the integers.
 * @docoff
 * @end[doc]
 *)
interactive add_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i IN int } -->
   sequent [squash] { 'H >- 'j IN int } -->
   sequent ['ext] { 'H >- add{'i; 'j} IN int }

interactive sub_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i IN int } -->
   sequent [squash] { 'H >- 'j IN int } -->
   sequent ['ext] { 'H >- sub{'i; 'j} IN int }

interactive mul_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i IN int } -->
   sequent [squash] { 'H >- 'j IN int } -->
   sequent ['ext] { 'H >- mul{'i; 'j} IN int }

interactive div_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i IN int } -->
   sequent [squash] { 'H >- 'j IN int } -->
   sequent [squash] { 'H >- not{.'j = 0 in int} } -->
   sequent ['ext] { 'H >- "div"{'i; 'j} IN int }

interactive rem_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i IN int } -->
   sequent [squash] { 'H >- 'j IN int } -->
   sequent [squash] { 'H >- not{.'j = 0 in int} } -->
   sequent ['ext] { 'H >- "rem"{'i; 'j} IN int }

interactive lt_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i IN int } -->
   sequent [squash] { 'H >- 'j IN int } -->
   sequent ['ext] { 'H >- "type"{lt{'i; 'j}} }

interactive gt_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i IN int } -->
   sequent [squash] { 'H >- 'j IN int } -->
   sequent ['ext] { 'H >- "type"{gt{'i; 'j}} }

interactive le_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i IN int } -->
   sequent [squash] { 'H >- 'j IN int } -->
   sequent ['ext] { 'H >- "type"{le{'i; 'j}} }

interactive ge_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i IN int } -->
   sequent [squash] { 'H >- 'j IN int } -->
   sequent ['ext] { 'H >- "type"{ge{'i; 'j}} }

interactive gt_member {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i IN int } -->
   sequent [squash] { 'H >- 'j IN int } -->
   sequent ['ext] { 'H >- gt{'i; 'j} IN univ[i:l] }

interactive le_member {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i IN int } -->
   sequent [squash] { 'H >- 'j IN int } -->
   sequent ['ext] { 'H >- le{'i; 'j} IN univ[i:l] }

interactive ge_member {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i IN int } -->
   sequent [squash] { 'H >- 'j IN int } -->
   sequent ['ext] { 'H >- ge{'i; 'j} IN univ[i:l] }

interactive lt_reverse {| elim [] |} 'H 'J 'y :
   sequent ['ext] { 'H; x: ('i < 'j); 'J['x]; y: "not"{.'j < 'i} >- 'C['x] } -->
   sequent ['ext] { 'H; x: ('i < 'j); 'J['x] >- 'C['x] }

interactive lt_add {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i < 'j } -->
   sequent ['ext] { 'H >- ('i +@ 'k) < ('j +@ 'k) }

interactive lt_sub {| intro [] |} 'H :
   sequent [squash] { 'H >- 'i < 'j } -->
   sequent ['ext] { 'H >- ('i -@ 'k) < ('j -@ 'k) }

interactive decide_lt 'H 'i 'j 'w :
   [wf] sequent [squash] { 'H >- 'i IN int } -->
   [wf] sequent [squash] { 'H >- 'j IN int } -->
   [main] sequent ['ext] { 'H; w: 'i < 'j >- 'C } -->
   [main] sequent ['ext] { 'H; w: "not"{.'i < 'j} >- 'C } -->
   sequent ['ext] { 'H >- 'C }

interactive decide_eq 'H 'i 'j 'w :
   [wf] sequent [squash] { 'H >- 'i IN int } -->
   [wf] sequent [squash] { 'H >- 'j IN int } -->
   [main] sequent ['ext] { 'H; w: 'i = 'j in int >- 'C } -->
   [main] sequent ['ext] { 'H; w: "not"{.'i = 'j in int} >- 'C } -->
   sequent ['ext] { 'H >- 'C }

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D
 *)
let zero = << 0 >>

(*
 * Squiggle.
 *)
let intSqequalT p =
   int_sqequal (Sequent.hyp_count_addr p) p

(*
 * Decision.
 *)
let decideT t p =
      let w = maybe_new_vars1 p "w" in
   if is_lt_term t then
      let t1, t2 = dest_lt t in
         decide_lt (Sequent.hyp_count_addr p) t1 t2 w p
   else if is_equal_term t then
      let typ, t1, t2 = dest_equal t in
         if is_int_term typ then
            decide_eq (Sequent.hyp_count_addr p) t1 t2 w p
         else
            raise (RefineError ("decideT", StringTermError ("type is not int", typ)))
   else
      raise (RefineError ("decideT", StringTermError ("can't decide", t)))

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of int.
 *)
let resource typeinf += (int_term, infer_univ1)

(*
 * Type of number.
 *)
let resource typeinf += (number_term, Typeinf.infer_const int_term)

(*
 * Type of ind.
 *)
let inf_ind inf consts decls eqs opt_eqs defs t =
   let i, a, b, down, base, c, d, up = dest_ind t in
   let eqs', opt_eqs', defs', i' = inf consts decls eqs opt_eqs defs i in
   inf consts decls eqs' ((i', int_term)::opt_eqs') defs' base

let resource typeinf += (ind_term, inf_ind)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
