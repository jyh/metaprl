(*
 * Function Intermediate Representation formalized in MetaPRL.
 *
 * Defines the types in the FIR.
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

open Refiner.Refiner.Term

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Integer and floating point precision.
 * The floating point precision terms are here for completeness.
 *    It'll be a while before we do any work with floating point numbers.
 *)

declare int8
declare int16
declare int32
declare int64
declare floatSingle
declare floatDouble
declare floatLongDouble

(* Integer type. *)

declare tyInt

(*
 * Enumeration type.
 * Represents a set of integers from 0 to ('num - 1).
 *)

declare tyEnum{ 'num }

(*
 * Native data types.
 * 'precision is the precision (number of bits).
 * 'sign should be val_true or val_false if this is, respectively,
 *    a signed or unsigned integral type.
 *)

declare tyRawInt{ 'precision; 'sign }
declare tyFloat{ 'precision }

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

declare tyUnion{ 'ty_var; 'ty_list; 'int_set }
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
 *)

declare val_true
declare val_false

(*************************************************************************
 * Term operations.
 *************************************************************************)

(*
 * Precisions.
 *)

val int8_term : term
val is_int8_term : term -> bool

val int16_term : term
val is_int16_term : term -> bool

val int32_term : term
val is_int32_term : term -> bool

val int64_term : term
val is_int64_term : term -> bool

val floatSingle_term : term
val is_floatSingle_term : term -> bool

val floatDouble_term : term
val is_floatDouble_term : term -> bool

val floatLongDouble_term : term
val is_floatLongDouble_term : term -> bool

(*
 * Integer type.
 *)

val tyInt_term : term
val is_tyInt_term : term -> bool

(*
 * Enumeration type.
 *)

val tyEnum_term : term
val is_tyEnum_term : term -> bool
val mk_tyEnum_term : term -> term
val dest_tyEnum_term : term -> term

(*
 * Native data types.
 *)

val tyRawInt_term : term
val is_tyRawInt_term : term -> bool
val mk_tyRawInt_term : term -> term -> term
val dest_tyRawInt_term : term -> term * term

val tyFloat_term : term
val is_tyFloat_term : term -> bool
val mk_tyFloat_term : term -> term
val dest_tyFloat_term : term -> term

(*
 * Function type.
 *)

val tyFun_term : term
val is_tyFun_term : term -> bool
val mk_tyFun_term : term -> term -> term
val dest_tyFun_term : term -> term * term

(*
 * Tuples.
 *)

val tyUnion_term : term
val is_tyUnion_term : term -> bool
val mk_tyUnion_term : term -> term -> term -> term
val dest_tyUnion_term : term -> term * term * term

val tyTuple_term : term
val is_tyTuple_term : term -> bool
val mk_tyTuple_term : term -> term
val dest_tyTuple_term : term -> term

val tyArray_term : term
val is_tyArray_term : term -> bool
val mk_tyArray_term : term -> term
val dest_tyArray_term : term -> term

val tyRawData_term : term
val is_tyRawData_term : term -> bool

(*
 * Polymorphism.
 *)

val tyVar_term : term
val is_tyVar_term : term -> bool
val mk_tyVar_term : term -> term
val dest_tyVar_term : term -> term

val tyApply_term : term
val is_tyApply_term : term -> bool
val mk_tyApply_term : term -> term -> term
val dest_tyApply_term : term -> term * term

val tyExists_term : term
val is_tyExists_term : term -> bool
val mk_tyExists_term : term -> term -> term
val dest_tyExists_term : term -> term * term

val tyAll_term : term
val is_tyAll_term : term -> bool
val mk_tyAll_term : term -> term -> term
val dest_tyAll_term : term -> term * term

val tyProject_term : term
val is_tyProject_term : term -> bool
val mk_tyProject_term : term -> term -> term
val dest_tyProject_term : term -> term * term

(*
 * Delayed type.
 *)

val tyDelayed_term : term
val is_tyDelayed_term : term -> bool

(*
 * Union tags.
 *)

val normalUnion_term : term
val is_normalUnion_term : term -> bool

val exnUnion_term : term
val is_exnUnion_term : term -> bool

(*
 * Defining types.
 *)

val unionElt_term : term
val is_unionElt_term : term -> bool
val mk_unionElt_term : term -> term -> term
val dest_unionElt_term : term -> term * term

val tyDefUnion_term : term
val is_tyDefUnion_term : term -> bool
val mk_tyDefUnion_term : term -> term -> term -> term
val dest_tyDefUnion_term : term -> term * term * term

val tyDefLambda_term : term
val is_tyDefLambda_term : term -> bool
val mk_tyDefLambda_term : term -> term -> term
val dest_tyDefLambda_term : term -> term * term

(*
 * Boolean type.
 *)

val val_true_term : term
val is_val_true_term : term -> bool

val val_false_term : term
val is_val_false_term : term -> bool
