(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define a type system for FIR expressions.
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
   produces_match{ 'key; cons{ matchCase{'set; s. 'e}; 'el } } <-->
   ifthenelse{ member{ 'key; 'set };
      btrue;
      produces_match{ 'key; 'el } }

(* Automation for rewrites. *)
let resource reduce += [
   << produces_match{ 'key; nil } >>, reduce_produces_match_base;
   << produces_match{ 'key; cons{ matchCase{'set; s. 'e}; 'el } } >>,
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
   [wf] sequent ['ext] { 'H >- 'state1 = 'state2 in ty_state } -->
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext]
      { 'H >- unop_exp{'op1; 'a} = unop_exp{'op2; 'b} in 'ty1 } -->
   [wf] sequent ['ext] { 'H; s: ty_state; v: 'ty1 >-
      'e1['s; 'v] = 'e2['s; 'v] in 'T } -->
   sequent ['ext] { 'H >-
      letUnop{ 'state1; 'op1; 'ty1; 'a; s1, v1. 'e1['s1; 'v1] } =
      letUnop{ 'state2; 'op2; 'ty2; 'b; s2, v2. 'e2['s2; 'v2] } in 'T }
   = it

prim letBinop_equality {| intro [] |} 'H 's 'v :
   [wf] sequent ['ext] { 'H >- 'state1 = 'state2 in ty_state } -->
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >-
      binop_exp{'op1; 'a1; 'a2} = binop_exp{'op2; 'b1; 'b2} in 'ty1 } -->
   [wf] sequent ['ext] { 'H; s: ty_state; v: 'ty1 >-
      'e1['s; 'v] = 'e2['s; 'v] in 'T } -->
   sequent ['ext] { 'H >-
      letBinop{ 'state1; 'op1; 'ty1; 'a1; 'a2; s1, v1. 'e1['s1; 'v1] } =
      letBinop{ 'state2; 'op2; 'ty2; 'b1; 'b2; s2, v2. 'e2['s2; 'v2] } in 'T }
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
   [wf] sequent ['ext] { 'H; s: ty_state >- 'e1['s] = 'e2['s] in 'T } -->
   sequent ['ext] { 'H >-
      matchCase{'k1; s1. 'e1['s1]} =
      matchCase{'k2; s2. 'e2['s2]} in 'T }
   = it

prim match_int_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'state1 = 'state2 in ty_state } -->
   [wf] sequent ['ext] { 'H >- 'i = 'j in int } -->
   [wf] sequent ['ext] { 'H >- 'cases1 = 'cases2 in array{'T} } -->
(*
   [main] sequent ['ext] { 'H >-
      "assert"{ produces_match{ number[i:n]; 'cases1 } } } -->
*)
   sequent ['ext] { 'H >-
      match_int{ 'state1; 'i; 'cases1 } =
      match_int{ 'state2; 'j; 'cases2 } in 'T }
   = it

prim match_block_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'state1 = 'state2 in ty_state } -->
   [wf] sequent ['ext] { 'H >- 'cases1 = 'cases2 in array{'T} } -->
   [wf] sequent ['ext] { 'H >- 'i = 'j in ty_block } -->
(*
   [main] sequent ['ext] { 'H >-
      "assert"{ produces_match{ 'i; 'cases1 } } } -->
*)
   sequent ['ext] { 'H >-
      match_block{ 'state1; 'i; 'cases1 } =
      match_block{ 'state2; 'j; 'cases2 } in 'T }
   = it

(*
 * Allocation operators and expressions.
 *)

prim ty_alloc_op_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- ty_alloc_op = ty_alloc_op in fir_univ }
   = it

prim allocTuple_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'list1 = 'list2 in array{fir_value} } -->
   sequent ['ext] { 'H >-
      allocTuple{'ty1; 'list1} =
      allocTuple{'ty2; 'list2} in ty_alloc_op }
   = it

prim allocArray_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'list1 = 'list2 in array{fir_value} } -->
   sequent ['ext] { 'H >-
      allocArray{'ty1; 'list1} =
      allocArray{'ty2; 'list2} in ty_alloc_op }
   = it

prim letAlloc_equality {| intro [] |} 'H 's 'v :
   [wf] sequent ['ext] { 'H >- 'state1 = 'state2 in ty_state } -->
   [wf] sequent ['ext] { 'H >- 'alloc_op1 = 'alloc_op2 in ty_alloc_op } -->
   [main] sequent ['ext] { 'H; s: ty_state; v: ty_ref >-
      'e1['s; 'v] = 'e2['s; 'v] in 'T } -->
   sequent ['ext] { 'H >-
      letAlloc{ 'state1; 'alloc_op1; s1, v1. 'e1['s1; 'v1] } =
      letAlloc{ 'state2; 'alloc_op2; s2, v2. 'e2['s2; 'v2] } in 'T }
   = it

(*
 * Subscripting operators and expressions.
 * We're completely ignoring the subscripting operators at the moment.
 * We're also not requiring that references/indices be in bounds.
 *)

prim letSubscript_equality {| intro [] |} 'H 's 'v :
   [wf] sequent ['ext] { 'H >- 'st1 = 'st2 in ty_state } -->
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'r1 = 'r2 in ty_ref } -->
   [wf] sequent ['ext] { 'H >- 'i1 = 'i2 in int } -->
   [main] sequent ['ext] { 'H; s: ty_state; v: 'ty1 >-
      'e1['s; 'v] = 'e1['s; 'v] in 'T } -->
   sequent ['ext] { 'H >-
      letSubscript{ 'st1; 'op1; 'ty1; 'r1; 'i1; s1, v1. 'e1['s1; 'v1] } =
      letSubscript{ 'st2; 'op2; 'ty2; 'r2; 'i2; s2, v2. 'e2['s2; 'v2] } in 'T }
   = it

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
