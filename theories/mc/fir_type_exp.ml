(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define a type system for FIR expressions.
 *)

include Base_theory
include Itt_equal
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
 * Rules.
 *************************************************************************)

(*
 * LetUnop/LetBinop equality. Note that 'T is the type 'e[v] and that
 *    the equality here is intensional.
 * To prove { 'H >- op_exp{'op1; 'a1} = op_exp{'op2; 'a2} in 'ty1 },
 *    it may be necessary to first apply rwh reduceC 0 and then
 *    prove the resulting sequent, as all op_exp's should reduce
 *    to some simpler form that can be worked with (they're all
 *    integer related at the moment, so this shouldn't be a problem).
 *)

(***
 * I question the v: ty1, s: ty_state stuff...
 * suppose 'e1 has fetches...and s is empty...does that type check
 * or not? what about dividing by v in 'e1 when v is zero??
 ***)

prim letUnop_equality {| intro [] |} 'H :
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

prim letBinop_equality {| intro [] |} 'H :
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

(*
 * Match equality.
 * As in LetOp, the equality here is intentional.  We need two
 *    equalities, one for matching on integers, and one for
 *    matching on blocks.
 *)

(***
 * Better way to automate?  the selT won't go, but I can make other
 * aspects that show up easier I think...
 * and is there a better split for int matching and block matching...
 * then again, the split here is the same as in Fir_exp for reduction
 ***)

prim produces_match_base {| intro [SelectOption 1] |} 'H :
   [main] sequent ['ext] { 'H >- "assert"{member{'num; 'set}} } -->
   sequent ['ext]
      { 'H >- produces_match{ 'num; cons{matchCase{'set; s. 'exp['s]}; 't} } }
   = it

prim produces_match_ind {| intro [SelectOption 2] |} 'H :
   [main] sequent ['ext] { 'H >- "assert"{bnot{member{'num; 'set}}} } -->
   [main] sequent ['ext] { 'H >- produces_match{ 'num; 't } } -->
   sequent ['ext]
      { 'H >- produces_match{ 'num; cons{matchCase{'set; s. 'exp['s]}; 't} } }
   = it

(***
 * ditto concern about s: ty_state
 ***)

prim matchCase_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'k1 = 'k2 in ty_int_set } -->
   [wf] sequent ['ext] { 'H; s: ty_state >- 'e1['s] = 'e2['s] in 'T } -->
   sequent ['ext] { 'H >-
      matchCase{'k1; s1. 'e1['s1]} =
      matchCase{'k2; s2. 'e2['s2]} in 'T }
   = it

prim match_int_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'state1 = 'state2 in ty_state } -->
   [wf] sequent ['ext] { 'H >- number[i:n] = number[j:n] in int } -->
   [wf] sequent ['ext] { 'H >- 'cases1 = 'cases2 in array{'T} } -->
   [main] sequent ['ext] { 'H >- produces_match{ number[i:n]; 'cases1 } } -->
   sequent ['ext] { 'H >-
      "match"{ 'state1; number[i:n]; 'cases1 } =
      "match"{ 'state2; number[j:n]; 'cases2 } in 'T }
   = it

prim match_block_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'state1 = 'state2 in ty_state } -->
   [wf] sequent ['ext] { 'H >- 'cases1 = 'cases2 in array{'T} } -->
   [wf] sequent ['ext]
      { 'H >- block{'i; 'args1} = block{'j; 'args2} in ty_block } -->
   [main] sequent ['ext] { 'H >- produces_match{ 'i; 'cases1 } } -->
   sequent ['ext] { 'H >-
      "match"{ 'state1; block{'i; 'args1}; 'cases1 } =
      "match"{ 'state2; block{'j; 'args2}; 'cases2 } in 'T }
   = it

(*
 * Allocation operators.
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

(****
 * same concern about s: ty_state, etc...
 ****)

prim letAlloc_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'state1 = 'state2 in ty_state } -->
   [wf] sequent ['ext] { 'H >- 'alloc_op1 = 'alloc_op2 in ty_alloc_op } -->
   [main] sequent ['ext] { 'H; s: ty_state; v: ty_ref >-
      'e1['s; 'v] = 'e2['s; 'v] in 'T } -->
   sequent ['ext] { 'H >-
      letAlloc{ 'state1; 'alloc_op1; s1, v1. 'e1['s1; 'v1] } =
      letAlloc{ 'state2; 'alloc_op2; s2, v2. 'e2['s2; 'v2] } in 'T }
   = it

(*
 * Subscripting operators.
 *)

(****
 * same concern about s: ty_state, etc...
 ****)

prim letSubscript_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'state1 = 'state2 in ty_state } -->
   [wf] sequent ['ext] { 'H >- 'ref1 = 'ref2 in ty_ref } -->
   [wf] sequent ['ext] { 'H >- 'index1 = 'index2 in int } -->
   [main] sequent ['ext] { 'H; s: ty_state; v: fir_value >-
      'e1['s; 'v] = 'e2['s; 'v] in 'T } -->
(* assertions about actually being able to fetch that? *)
   sequent ['ext] { 'H >-
      letSubscript{ 'state1; 'ref1; 'index1; s1, v1. 'e1['s1; 'v1] } =
      letSubscript{ 'state2; 'ref2; 'index2; s2, v2. 'e2['s2; 'v2] } in 'T }
   = it

prim setSubscript_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'state1 = 'state2 in ty_state } -->
   [wf] sequent ['ext] { 'H >- 'ref1 = 'ref2 in ty_ref } -->
   [wf] sequent ['ext] { 'H >- 'index1 = 'index2 in int } -->
   [wf] sequent ['ext] { 'H >- 'val1 = 'val2 in fir_value } -->
   [main] sequent ['ext] { 'H; s: ty_state >- 'e1['s] = 'e2['s] in 'T } -->
(* assertions about being able to set that location?? *)
   sequent ['ext] { 'H >-
      setSubscript{ 'state1; 'ref1; 'index1; 'val1; s1. 'e1['s1] } =
      setSubscript{ 'state2; 'ref2; 'index2; 'val2; s2. 'e2['s2] } in 'T }
   = it
