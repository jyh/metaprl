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

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Judgement that a match statement produces a match. *)
dform produces_match_df : except_mode[src] :: produces_match{ 'key; 'cases } =
   `"produces_match(" slot{'key} `", " slot{'cases} `")"

(*************************************************************************
 * Rules.
 *************************************************************************)

(*
 * Program equality.
 *)

(***
 * I'm not sure if I like the following...
 * it assumes that 'e1 and 'e2 are independent of the state,
 * which they don't have to be...
 ***)

prim prog_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- 's1 = 's2 in ty_state } -->
   sequent ['ext] { 'H >- 'e1 = 'e2 in 'T } -->
   sequent ['ext] { 'H >- prog{ 's1; 'e1 } = prog{ 's2; 'e2 } in 'T }
   = it

(*
 * LetUnop/LetBinop equality. Note that 'T is the type 'e[v] and that
 *    the equality here is intensional.
 * To prove { 'H >- op_exp{'op1; 'a1} = op_exp{'op2; 'a2} in 'ty1 },
 *    it may be necessary to first apply rwh reduceC 0 and then
 *    prove the resulting sequent, as all op_exp's should reduce
 *    to some simpler form that can be worked with (they're all
 *    integer related at the moment, so this shouldn't be a problem).
 *)

prim letUnop_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext]
      { 'H >- unop_exp{'op1; 'a} = unop_exp{'op2; 'b} in 'ty1 } -->
   [wf] sequent ['ext] { 'H; v: 'ty1 >- 'e1['v] = 'e2['v] in 'T } -->
   sequent ['ext] { 'H >-
      letUnop{ 'op1; 'ty1; 'a; v1. 'e1['v1] } =
      letUnop{ 'op2; 'ty2; 'b; v2. 'e2['v2] } in 'T }
   = it

prim letBinop_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'ty1 = 'ty2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >-
      binop_exp{'op1; 'a1; 'a2} = binop_exp{'op2; 'b1; 'b2} in 'ty1 } -->
   [wf] sequent ['ext] { 'H; v: 'ty1 >- 'e1['v] = 'e2['v] in 'T } -->
   sequent ['ext] { 'H >-
      letBinop{ 'op1; 'ty1; 'a1; 'a2; v1. 'e1['v1] } =
      letBinop{ 'op2; 'ty2; 'b1; 'b2; v2. 'e2['v2] } in 'T }
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
 ***)

prim produces_match_base {| intro [SelectOption 1] |} 'H :
   [main] sequent ['ext] { 'H >- "assert"{member{'num; 'set}} } -->
   sequent ['ext]
      { 'H >- produces_match{ 'num; cons{matchCase{'set;'exp}; 't} } }
   = it

prim produces_match_ind {| intro [SelectOption 2] |} 'H :
   [main] sequent ['ext] { 'H >- "assert"{bnot{member{'num; 'set}}} } -->
   [main] sequent ['ext] { 'H >- produces_match{ 'num; 't } } -->
   sequent ['ext]
      { 'H >- produces_match{ 'num; cons{matchCase{'set;'exp}; 't} } }
   = it

prim matchCase_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'k1 = 'k2 in ty_int_set } -->
   [wf] sequent ['ext] { 'H >- 'e1 = 'e2 in 'T } -->
   sequent ['ext] { 'H >- matchCase{'k1; 'e1} = matchCase{'k2; 'e2} in 'T }
   = it

prim match_int_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- number[i:n] = number[j:n] in int } -->
   [wf] sequent ['ext] { 'H >- 'cases1 = 'cases2 in array{'T} } -->
   [main] sequent ['ext] { 'H >- produces_match{ number[i:n]; 'cases1 } } -->
   sequent ['ext] { 'H >-
      "match"{ number[i:n]; 'cases1 } = "match"{ number[j:n]; 'cases2 } in 'T }
   = it

prim match_block_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'cases1 = 'cases2 in array{'T} } -->
   [wf] sequent ['ext]
      { 'H >- block{'i; 'args1} = block{'j; 'args2} in ty_block } -->
   [main] sequent ['ext] { 'H >- produces_match{ 'i; 'cases1 } } -->
   sequent ['ext] { 'H >-
      "match"{ block{'i; 'args1}; 'cases1 } =
      "match"{ block{'j; 'args2}; 'cases2 } in 'T }
   = it

(*
prim match_int_equality {| intro [SelectOption 1] |} 'H :
   [wf] sequent ['ext] { 'H >- 'i = 'j in int } -->
   [wf] sequent ['ext] { 'H >- 'cases1 = 'cases2 in array{'T} } -->
   [wf] sequent ['ext] { 'H >- produces_match{ 'i; 'cases1 } } -->
   sequent ['ext] { 'H >-
      "match"{ 'i; 'cases1 } = "match"{ 'j; 'cases2 } in 'T }
   = it

prim match_block_equality {| intro [SelectOption 2] |} 'H :
   [wf] sequent ['ext] { 'H >- 'i = 'j in ty_block } -->
   [wf] sequent ['ext] { 'H >- 'cases1 = 'cases2 in array{'T} } -->
   [wf] sequent ['ext] { 'H >- produces_match{ 'i; 'cases1 } } -->
   sequent ['ext] { 'H >-
      "match"{ 'i; 'cases1 } = "match"{ 'j; 'cases2 } in 'T }
   = it
*)
