(*
 * Function Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Defines the type system for the FIR.
 *)

include Base_theory
include Itt_theory

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Integer type. *)
declare tyInt

(*
 *  Function type.
 * 'ty_list is a list of the types of the function's arguments.
 * 'ty is the type of the return value of the function.
 *)
declare tyFun{ 'ty_list; 'ty }

(*
 * Union type.
 * normalUnion and exnUnion are union types.
 * unionElt :
 *    'ty is a type.
 *    'bool is a mutable flag.
 * tyUnion :
 *    'union_ty is one of normalUnion and exnUnion.
 *    'elts is a list of unionElt lists.
 * This is intended to represent something like:
 *    type t =
 *       A of t11 * t12
 *     | B of t21
 *    ...
 *)
declare normalUnion
declare exnUnion
declare unionElt{ 'ty; 'bool }
declare tyUnion{ 'union_ty; 'elts }

(*
 * Array type.
 * 'ty is the type of elements in the array.
 *)
declare tyArray{ 'ty }

(*
 * Subscripting.
 * 't1 should be an array.
 * 't2 is the type of the index variable used to index the array.
 *)
declare tySubscript{ 't1; 't2 }

(*
 * Memory is allocated in blocks.
 * Each block has a tag and some values (a list).
 *)
declare block{ 'tag; 'args }

(*
 * Boolean type.
 * tyBool is the type.  ftrue and ffalse represent true and false.
 * eq_fbool is for testing equality on booleans.
 *)
define unfold_tyBool : tyBool <-->
   tyUnion{ normalUnion; cons{ nil; cons{ nil; nil } } }
define unfold_ftrue : ftrue <--> block{ 1; nil }
define unfold_ffalse : ffalse <--> block{ 0; nil }
define unfold_eq_fbool : eq_fbool{ block{'a1; nil}; block{'a2; nil} } <-->
   beq_int{ 'a1; 'a2 }

(*
 * Integer atom.
 * 'int is the integer itself (a number).
 *)
declare atomInt{ 'int }

(*
 * Variable atom.
 * 'var is the variable itself.
 * 'ty is the type of the variable.
 *)
declare atomVar{ 'var; 'ty }
