(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define a type system for FIR expressions.
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
 * Author: Brian Emre Aydemir
 * Email:  emre@its.caltech.edu
 *)

include Base_theory
include Itt_theory
include Fir_int_set
include Fir_exp
include Fir_type
include Fir_type_state

open Base_dtactic

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Judgement that a match statement produces a match. *)
declare produces_match{ 'key; 'cases }

(* Allocation operator type. *)
declare ty_alloc_op

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Judgement that a match statement produces a match. *)
dform produces_match_df : except_mode[src] :: produces_match{ 'key; 'cases } =
   `"produces_match(" slot{'key} `", " slot{'cases} `")"

(* Allocation operator type. *)
dform ty_alloc_op_df : except_mode[src] :: ty_alloc_op =
   `"Ty_alloc_op"

(*************************************************************************
 * Rewrites.
 *************************************************************************)

prim_rw reduce_produces_match_base :
   produces_match{ 'key; nil } <-->
   bfalse
prim_rw reduce_produces_match_ind :
   produces_match{ 'key; cons{ matchCase{'set; 'e}; 'el } } <-->
   ifthenelse{ member{ 'key; 'set };
      btrue;
      produces_match{ 'key; 'el } }

(* Automation for rewrites. *)
let resource reduce += [
   << produces_match{ 'key; nil } >>, reduce_produces_match_base;
   << produces_match{ 'key; cons{ matchCase{'set; 'e}; 'el } } >>,
      reduce_produces_match_ind
]

(*************************************************************************
 * Rules.
 *************************************************************************)

(*
 * LetUnop/LetBinop equality. Note that 'T is the type 'e[v] and that
 *    the equality here is intensional.
 *)

prim letUnop_equality {| intro [] |} 'H 's 'v :
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext]
      { 'H >- unop_exp{'op1; 'a} = unop_exp{'op2; 'b} in 'ty1 } -->
   [wf] sequent ['ext] { 'H; v: 'ty1 >- 'e1['v] = 'e2['v] in 'T } -->
   sequent ['ext] { 'H >-
      letUnop{ 'op1; 'ty1; 'a;  v1. 'e1['v1] } =
      letUnop{ 'op2; 'ty2; 'b;  v2. 'e2['v2] } in 'T }
   = it

prim letBinop_equality {| intro [] |} 'H 's 'v :
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >-
      binop_exp{'op1; 'a1; 'a2} = binop_exp{'op2; 'b1; 'b2} in 'ty1 } -->
   [wf] sequent ['ext] { 'H; v: 'ty1 >- 'e1['v] = 'e2['v] in 'T } -->
   sequent ['ext] { 'H >-
      letBinop{ 'op1; 'ty1; 'a1; 'a2; v1. 'e1['v1] } =
      letBinop{ 'op2; 'ty2; 'b1; 'b2; v2. 'e2['v2] } in 'T }
   = it

interactive idOp_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'a1 = 'a2 in 'T } -->
   sequent ['ext] { 'H >- unop_exp{ idOp; 'a1 } = unop_exp{ idOp; 'a2 } in 'T }

(*
 * Match equality.
 * As in LetOp, the equality here is intentional.
 *)

prim matchCase_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'k1 = 'k2 in ty_int_set } -->
   [wf] sequent ['ext] { 'H >- 'e1 = 'e2 in 'T } -->
   sequent ['ext] { 'H >- matchCase{'k1; 'e1} = matchCase{'k2; 'e2} in 'T }
   = it

prim match_int_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- number[i:n] = number[j:n] in int } -->
   [wf] sequent ['ext] { 'H >- 'cases1 = 'cases2 in array{'T} } -->
(*
   [main] sequent ['ext] { 'H >-
      "assert"{ produces_match{ number[i:n]; 'cases1 } } } -->
*)
   sequent ['ext] { 'H >-
      "match"{ number[i:n]; 'cases1 } =
      "match"{ number[j:n]; 'cases2 } in 'T }
   = it

prim match_block_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'cases1 = 'cases2 in array{'T} } -->
   [wf] sequent ['ext] { 'H >- 'i = 'j in int } -->
(*
   [main] sequent ['ext] { 'H >-
      "assert"{ produces_match{ 'i; 'cases1 } } } -->
*)
   sequent ['ext] { 'H >-
      "match"{ block{'i; 'args}; 'cases1 } =
      "match"{ block{'j; 'args}; 'cases2 } in 'T }
   = it

(*
 * Allocation operators and expressions.
 *)

prim ty_alloc_op_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- ty_alloc_op = ty_alloc_op in fir_univ }
   = it

(* Incorrect I think. *)
prim allocTuple_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'list1 = 'list2 in array{fir_value} } -->
   sequent ['ext] { 'H >-
      allocTuple{'ty1; 'list1} =
      allocTuple{'ty2; 'list2} in ty_alloc_op }
   = it

(* Incorrect I think. *)
prim allocArray_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'list1 = 'list2 in array{fir_value} } -->
   sequent ['ext] { 'H >-
      allocArray{'ty1; 'list1} =
      allocArray{'ty2; 'list2} in ty_alloc_op }
   = it

(* Incorrect I think. *)
prim allocUnion_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   (* ty_var things should go here... *)
   [wf] sequent ['ext] { 'H >- 'num1 = 'num2 in int } -->
   [wf] sequent ['ext] { 'H >- 'list1 = 'list2 in array{fir_value} } -->
   sequent ['ext] { 'H >-
      allocUnion{'ty1; 'ty_var1; 'num1; 'list1 } =
      allocUnion{'ty2; 'ty_var2; 'num2; 'list2 } in ty_alloc_op }
   = it

(* Need to be corrected / updated. *)
(*
prim letAlloc_equality {| intro [] |} 'H 's 'v :
   [wf] sequent ['ext] { 'H >- 'alloc_op1 = 'alloc_op2 in ty_alloc_op } -->
   [main] sequent ['ext] { 'H; s: ty_state; v: ty_ref >-
      'e1['s; 'v] = 'e2['s; 'v] in 'T } -->
   sequent ['ext] { 'H >-
      letAlloc{ 'state1; 'alloc_op1; s1, v1. 'e1['s1; 'v1] } =
      letAlloc{ 'state2; 'alloc_op2; s2, v2. 'e2['s2; 'v2] } in 'T }
   = it
*)

(*
 * Subscripting operators and expressions.
 * We're completely ignoring the subscripting operators at the moment.
 * We're also not requiring that references/indices be in bounds.
 *)

(* Needs to be corrected / updated. *)
(*
prim letSubscript_equality {| intro [] |} 'H 's 'v :
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'r1 = 'r2 in ty_ref } -->
   [wf] sequent ['ext] { 'H >- 'i1 = 'i2 in int } -->
   [main] sequent ['ext] { 'H; s: ty_state; v: 'ty1 >-
      'e1['s; 'v] = 'e1['s; 'v] in 'T } -->
   sequent ['ext] { 'H >-
      letSubscript{ 'st1; 'op1; 'ty1; 'r1; 'i1; s1, v1. 'e1['s1; 'v1] } =
      letSubscript{ 'st2; 'op2; 'ty2; 'r2; 'i2; s2, v2. 'e2['s2; 'v2] } in 'T }
   = it

(* Needs to be corrected / updated. *)
prim setSubscript_equality {| intro [] |} 'H 's :
   [wf] sequent ['ext] { 'H >- 'st1 = 'st2 in ty_state } -->
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'r1 = 'r2 in ty_ref } -->
   [wf] sequent ['ext] { 'H >- 'i1 = 'i2 in int } -->
   [wf] sequent ['ext] { 'H >- 'n1 = 'n2 in 'ty1 } -->
   [main] sequent ['ext] { 'H; s: ty_state >- 'e1['s] = 'e2['s] in 'T } -->
   sequent ['ext] { 'H >-
      setSubscript{ 'st1; 'op1; 'ty1; 'r1; 'i1; 'n1; s1. 'e1['s1] } =
      setSubscript{ 'st2; 'op2; 'ty2; 'r2; 'i2; 'n2; s2. 'e2['s2] } in 'T }
   = it
*)
