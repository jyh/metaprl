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

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Identity (polymorphic). *)
declare idOp

(* Pointer equality. *)
declare eqEqOp
declare neqEqOp

(* Subscript operators. *)
declare blockPolySub
declare rawDataSub
declare rawFunctionSub

(* Allocation operators. *)
declare allocTuple{ 'ty; 'atom_list }
declare allocArray{ 'ty; 'atom_list }
declare allocUnion{ 'ty; 'ty_var; 'num; 'atom_list }
declare allocMalloc{ 'atom }

(*
 * Normal values.
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
declare letExt{ 'ty; 'string; 'ty_str; 'atom_list; v. 'exp['v] }
declare tailCall{ 'var; 'atom_list }

(* Control. *)
declare matchCase{ 'set; s. 'exp['s] }
declare match_int{ 'state; 'key; 'cases }
declare match_block{ 'state; 'key; 'cases }

(* Allocation. *)
declare letAlloc{ 'state; 'alloc_op; s, v. 'exp['s; 'v] }

(* Subscripting. *)
declare letSubscript{ 'state; 'subop; 'ty; 'ref; 'index; s, v. 'exp['s; 'v] }
declare setSubscript{ 'state; 'subop; 'ty; 'ref; 'index;
                      'new_val; s. 'exp['s] }

(*************************************************************************
 * Rewrites.
 *************************************************************************)

topval reduce_idOp : conv
topval reduce_eqEqOp : conv
topval reduce_neqEqOp : conv
topval reduce_atomInt : conv
topval reduce_atomEnum : conv
topval reduce_atomVar : conv
topval reduce_letUnop : conv
topval reduce_letBinop : conv
topval reduce_allocTuple : conv
topval reduce_allocArray : conv
topval reduce_allocUnion : conv
topval reduce_match_int : conv
topval reduce_match_block : conv
topval reduce_letSubscript : conv
topval reduce_setSubscript : conv
