(*
 * The Mp_mc_fir_ty module defines terms to represent FIR types.
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
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
 * Term declarations.
 *************************************************************************)

(* Base types. *)

declare tyInt
declare tyEnum{ 'int }

(* Native types. *)

declare tyRawInt{ 'int_precision; 'int_signed }
declare tyFloat{ 'float_precision }

(* Functions. *)

declare tyFun{ 'ty_list; 'ty }

(* Tuples. *)

declare tyUnion{ 'ty_var; 'ty_list; 'int_set }
declare tyTuple{ 'tuple_class; 'ty_list }
declare tyArray{ 'ty }
declare tyRawData
declare tyPointer{ 'sub_block }
declare tyFrame{ 'label }

(* Polymorphism. *)

declare tyVar{ 'ty_var }
declare tyApply{ 'ty_var; 'ty_list }
declare tyExists{ 'ty_var_list; 'ty }
declare tyAll{ 'ty_var_list; 'ty }
declare tyProject{ 'var; 'int }

(* Object-oriented. *)

declare tyCase{ 'ty }
declare tyObject{ 'ty_var; 'ty }

(* Delayed type. *)

declare tyDelayed

(* Defining types. *)

declare unionElt{ 'ty; 'bool }
declare tyDefUnion{ 'ty_var_list; 'union_type; 'elts }
declare tyDefLambda{ 'ty_var_list; 'ty }

(*************************************************************************
 * Term operations.
 *************************************************************************)

(* Base types. *)

val tyInt_term : term
val is_tyInt_term : term -> bool

val tyEnum_term : term
val is_tyEnum_term : term -> bool
val mk_tyEnum_term : term -> term
val dest_tyEnum_term : term -> term

(* Native types. *)

val tyRawInt_term : term
val is_tyRawInt_term : term -> bool
val mk_tyRawInt_term : term -> term -> term
val dest_tyRawInt_term : term -> term * term

val tyFloat_term : term
val is_tyFloat_term : term -> bool
val mk_tyFloat_term : term -> term
val dest_tyFloat_term : term -> term

(* Functions. *)

val tyFun_term : term
val is_tyFun_term : term -> bool
val mk_tyFun_term : term -> term -> term
val dest_tyFun_term : term -> term * term

(* Tuples. *)

val tyUnion_term : term
val is_tyUnion_term : term -> bool
val mk_tyUnion_term : term -> term -> term -> term
val dest_tyUnion_term : term -> term * term * term

val tyTuple_term : term
val is_tyTuple_term : term -> bool
val mk_tyTuple_term : term -> term -> term
val dest_tyTuple_term : term -> term * term

val tyArray_term : term
val is_tyArray_term : term -> bool
val mk_tyArray_term : term -> term
val dest_tyArray_term : term -> term

val tyRawData_term : term
val is_tyRawData_term : term -> bool

val tyPointer_term : term
val is_tyPointer_term : term -> bool
val mk_tyPointer_term : term -> term
val dest_tyPointer_term : term -> term

val tyFrame_term : term
val is_tyFrame_term : term -> bool
val mk_tyFrame_term : term -> term
val dest_tyFrame_term : term -> term

(* Polymorphism *)

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

(* Object-oriented. *)

val tyCase_term : term
val is_tyCase_term : term -> bool
val mk_tyCase_term : term -> term
val dest_tyCase_term : term -> term

val tyObject_term : term
val is_tyObject_term : term -> bool
val mk_tyObject_term : term -> term -> term
val dest_tyObject_term : term -> term * term

(* Delayed type. *)

val tyDelayed_term : term
val is_tyDelayed_term : term -> bool

(* Defining types. *)

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
