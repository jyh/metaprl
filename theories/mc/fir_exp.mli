(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define and implement the basic expression forms in the FIR.
 *)

include Base_theory
include Itt_theory
include Fir_state
include Fir_int_set
include Fir_ty

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Identity (polymorphic). *)
declare idOp

(*
 * Allocation operators.
 * copy makes a list with 'len copies of 'init.
 * 'len should be a positive number.
 *)
declare allocTuple{ 'ty; 'atom_list }
declare allocArray{ 'ty; 'atom_list }
declare allocUnion{ 'ty; 'ty_var; 'num; 'atom_list }
define unfold_copy : copy{ 'len; 'init } <-->
   ind{'len; i, j. nil; nil; i, j. cons{'init; 'j}}

(*
 * Normal values.
 *)

(* Subscript ops. *)
declare rawSubscript
declare intSubscript

(*
 * Normal atoms.
 * 'int in atomInt is the integer itself (a number).
 * 'bound and 'num in atomEnum are numbers satisfying 0 <= 'num < 'bound.
 * 'var in atomVar is the variable itself.
 *)
declare atomInt{ 'int }
declare atomEnum{ 'bound; 'num }
declare atomConst{ 'ty; 'ty_var; 'num }
declare atomVar{ 'var }

(*
 * Expressions.
 *)

(* Primitive operations. *)
declare unop_exp{ 'op; 'a1 }
declare binop_exp{ 'op; 'a1; 'a2 }
declare letUnop{ 'state; 'op; 'ty; 'a1; s, v. 'exp['s; 'v] }
declare letBinop{ 'state; 'op; 'ty; 'a1; 'a2; s, v. 'exp['s; 'v] }

(* Function application. *)
declare tailCall{ 'var; 'atom_list }

(* Control. *)
declare matchCase{ 'set; s. 'exp['s] }
declare "match"{ 'state; 'key; 'cases }

(* Allocation. *)
declare letAlloc{ 'state; 'alloc_op; s, v. 'exp['s; 'v] }

(* Subscripting. *)
declare letSubscript{ 'state; 'ref; 'index; s, v. 'exp['s; 'v] }
declare setSubscript{ 'state; 'ref; 'index; 'new_val; s. 'exp['s] }
