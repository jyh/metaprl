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

(*
 * Pointer equality.
 * Binary ops that evaluate as integer (in)equality.
 *)
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
 * atomInt evaluates to 'int (a number).
 * atomEnum evalutes to 'num (a number).
 * atomVar evaluates to 'var (a free variable).
 *)
declare atomInt{ 'int }
declare atomEnum{ 'bound; 'num }
declare atomConst{ 'ty; 'ty_var; 'num }
declare atomVar{ 'var }

(*
 * Expressions.
 *)

(*
 * Primitive operations.
 * We bind 'v to the value of ('op args).
 *)
declare unop_exp{ 'op; 'a1 }
declare binop_exp{ 'op; 'a1; 'a2 }
declare letUnop{ 'op; 'ty; 'a1; v. 'exp['v] }
declare letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp['v] }

(*
 * Function application.
 * letExt is treated as a no-op; it evaluates to 'exp[it].
 *)
declare letExt{ 'ty; 'string; 'ty_of_str; 'atom_list; v. 'exp['v] }
declare tailCall{ 'var; 'atom_list }

(*
 * Control.
 * A matchCase consists of an int_set an expression.
 * A match statement has a 'key (a number/int or block), and a list
 * of matchCases.
 *)
declare matchCase{ 'set; 'exp }
declare "match"{ 'key; 'cases }

(* Allocation. *)
declare letAlloc{ 'alloc_op; v. 'exp['v] }

(* Subscripting. *)
declare letSubscript{ 'subop; 'ty; 'ref; 'index; v. 'exp['v] }
declare setSubscript{ 'subop; 'ty; 'ref; 'index; 'new_val; 'exp }

(*
 * Misc.
 * Used in making output from the mc compiler more manageable.
 *)

declare unknownFun
declare unknownSet
declare unknownTy
declare unknownTydef
declare unknownAtom
declare unknownAlloc
declare unknownSubop

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
topval reduce_letExt : conv
topval reduce_match_int : conv
topval reduce_match_block : conv
topval reduce_allocTuple : conv
topval reduce_allocArray : conv
topval reduce_letSubscript : conv
