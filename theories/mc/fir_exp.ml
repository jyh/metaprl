(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define and implement the basic expression forms in the FIR.
 * See fir_exp.mli for a description of the terms below.
 *
 * Todo:
 *    -  Check implementations for correctness and consistancy, esp.
 *       letSubCheck since it's a nop right now.
 *    -  Use MetaPRL mechanisms for parenthesis and whatnot.
 *)

include Base_theory
include Itt_theory
include Fir_ty
include Fir_int_set

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Inlined operators.
 *)

(* Identity (polymorphic). *)
declare idOp

(*
 * Allocation operators.
 *)

declare allocSafe{ 'tag; 'args }
declare allocArray{ 'len; 'init }
define unfold_copy : copy{ 'len; 'init } <-->
   ind{'len; i, j. nil; nil; i, j. cons{'init; 'j}}

(*
 * Expressions.
 *)

(* Function application. *)
declare unOp{ 'op; 'a1; v. 'exp['v] }
declare binOp{ 'op; 'a1; 'a2; v. 'exp['v] }
(*declare tailCall*)

(* Control. *)
declare matchCase{ 'set; 'exp }
declare "match"{ 'a; 'cases }

(* Allocation. *)
declare letAlloc{ 'op; v. 'exp['v] }

(* Subscripting. *)
declare letSubscript{ 'block; 'index; v. 'exp['v] }
(*declare setSubscript{ 'a1; 'a2; 'a3; 'exp }*)
declare letSubCheck{ 'a1; 'a2; v1, v2. 'exp['v1; 'v2] }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Identity (polymorphic). *)
dform idOp_df : except_mode[src] :: idOp = `"id"

(* Allocation operators. *)
dform allocSafe_df : except_mode[src] :: allocSafe{ 'tag; 'args } =
   szone `"AllocSafe{" slot{'tag} `"; " slot{'args} `"}" ezone
dform allocArray_df : except_mode[src] :: allocArray{ 'len; 'init } =
   lzone `"AllocArray{" slot{'len} `"; " slot{'init} `"}" ezone
dform copy_df : except_mode[src] :: copy{ 'len; 'init} =
   lzone `"copy{" slot{'len} `"; " slot{'init} `"}" ezone

(* Function application. *)
dform unOp_df : except_mode[src] :: unOp{ 'op; 'a1; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone slot{'op} `"(" slot{'a1} `")" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform binOp_df : except_mode[src] :: binOp{ 'op; 'a1; 'a2; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone `"(" slot{'a1} `" " slot{'op} `" " slot{'a2} `")" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm

(* Control. *)
dform matchCase_df : except_mode[src] :: matchCase{ 'set; 'exp } =
   pushm[0] szone push_indent slot{'set} `" ->" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform match_df : except_mode[src] :: "match"{'a; 'cases } =
   pushm[0] szone push_indent `"match" hspace
   szone slot{'a} ezone popm hspace
   push_indent `"in" hspace
   szone slot{'cases} ezone popm
   ezone popm

(* Allocation *)
dform letAlloc_df : except_mode[src] :: letAlloc{ 'op; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone slot{'op} ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm

(* Subscripting. *)
dform letSubscript_df : except_mode[src] ::
   letSubscript{ 'block; 'index; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone slot{'block} `"[" slot{'index} `"]" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm
(* dform setSubscript_df : *)
(* dform letSubCheck_df : *)

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Identity (polymorphic). *)
prim_rw reduce_idOp : unOp{ idOp; 'a1; v. 'exp['v] } <--> 'exp['a1]

(* Allocation. *)
prim_rw reduce_allocSafe : letAlloc{ allocSafe{'tag; 'args}; v. 'exp['v] } <-->
   'exp[ block{'tag; 'args} ]
prim_rw reduce_allocArray :
   letAlloc{ allocArray{'len; 'init}; v. 'exp['v] } <-->
   'exp[ block{0; copy{'len; 'init}} ]

(* Control *)
prim_rw reduce_match_int :
   "match"{ number[i:n]; cons{matchCase{'set; 'exp}; 'el} } <-->
   ifthenelse{ member{number[i:n]; 'set}; 'exp; ."match"{number[i:n]; 'el} }
prim_rw reduce_match_block :
   "match"{ block{ 'i; 'args }; cons{matchCase{'set; 'exp}; 'el} } <-->
   ifthenelse{ member{'i; 'set}; 'exp; ."match"{block{'i; nil}; 'el} }

(* Subscripting. *)
prim_rw reduce_letSubscript :
   letSubscript{ block{'tag; 'args}; 'index; v. 'exp['v] } <-->
   'exp[ nth{'args; 'index} ]
prim_rw reduce_letSubCheck :
   letSubCheck{ 'a1; 'a2; v1, v2. 'exp['v1; 'v2] } <-->
   'exp['a1; 'a2]

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << unOp{ idOp; 'a1; v. 'exp['v] } >>, reduce_idOp;

   << letAlloc{ allocSafe{'tag; 'args}; v. 'exp['v] } >>, reduce_allocSafe;
   << letAlloc{ allocArray{'len; 'init}; v. 'exp['v] } >>, reduce_allocArray;
   << copy{ 'len; 'init } >>, unfold_copy;

   << "match"{ number[i:n]; cons{matchCase{'set; 'exp}; 'el} } >>,
      reduce_match_int;
   << "match"{ block{ 'i; 'args }; cons{matchCase{'set; 'exp}; 'el} } >>,
      reduce_match_block;

   << letSubscript{ block{'tag; 'args}; 'index; v. 'exp['v] } >>,
      reduce_letSubscript;
   << letSubCheck{ 'a1; 'a2; v1, v2. 'exp['v1; 'v2] } >>, reduce_letSubCheck
]
