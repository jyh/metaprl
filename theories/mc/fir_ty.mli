(*
 * Function Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Defines the type system in the FIR.
 *)

include Base_theory
include Fir_int_set

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Integer type. *)
declare tyInt

(*
 * Enumeration type.
 * Represents a set of integers from 0 to ('num - 1).
 * 'num should be a number.
 *)
declare tyEnum{ 'num }

(*
 *  Function type.
 * 'ty_list is a list of the types of the function's arguments.
 * 'ty is the type of the return value of the function.
 *)
declare tyFun{ 'ty_list; 'ty }

(*
 * Tuples.
 * 'ty_list in tyTuple is a list of the types in the tuple.
 * 'ty in tyArray is the type of the elements in the array.
 *)
declare tyUnion{ 'union_ty; 'ty_list; 'int_opt }
declare tyTuple{ 'ty_list }
declare tyArray{ 'ty }
declare tyRawData

(* Polymorphism. *)
declare tyVar{ 'ty_var }
declare tyApply{ 'ty_var; 'ty_list }
declare tyExists{ 'ty_var_list; 'ty }
declare tyAll{ 'ty_var_list; 'ty }
declare tyProject{ 'ty_var; 'num }

(*
 * Delayed type.
 * Type should be inferred later.
 *)
declare tyDelayed

(*
 * Union tags.
 * normalUnion : all the fields are known and ordered.
 * exnUnion : not all the fields are known, nor are they ordered.
 *)
declare normalUnion
declare exnUnion

(* Defining types. *)
declare unionElt{ 'ty; 'bool }
declare tyDefUnion{ 'ty_var_list; 'union_ty; 'elts }
declare tyDefLambda{ 'ty_var_list; 'ty }

(*
 * Boolean type.
 * true_set and false_set define true and false.
 *)
define unfold_true_set : true_set <--> int_set{ 1; 1 }
define unfold_false_set : false_set <--> int_set{ 0; 0 }
define unfold_val_true : val_true <--> 1
define unfold_val_false : val_false <--> 0

(* Functions. *)
declare lambda{ x. 'f['x] }
declare apply{ 'f; 'x }

(*************************************************************************
 * Rewrites.
 *************************************************************************)

topval unfold_true_set : conv
topval unfold_false_set : conv
topval unfold_val_true : conv
topval unfold_val_false : conv
topval beta_reduce : conv
