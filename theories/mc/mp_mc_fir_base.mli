(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define terms to represent FIR types and terms.
 * Specific FIR types represented here: int_set, rawint_set,
 * float_precision, int_precision, int_signed, tuple_class, union_type
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
 * Term declarations.
 *************************************************************************)

(* Options, i.e. None | Some of 'a. *)

declare noneOpt
declare someOpt{ 'a }

(* Boolean constants. *)

declare val_true
declare val_false

(* Floating-point and integer precisions. *)

declare int8
declare int16
declare int32
declare int64
declare floatSingle
declare floatDouble
declare floatLongDouble

(* Signed / unsigned integer qualifiers. *)

declare signedInt
declare unsignedInt

(* int and rawint sets. *)

declare interval{ 'left; 'right } (* closed bounds, i.e. [left, right] *)
declare int_set{ 'interval_list }
declare rawint_set{ 'int_precision; 'int_signed; 'interval_list }

(* Tuple classes. *)

declare normalTuple
declare rawTuple

(* Union tags. *)

declare normalUnion
declare exnUnion

(*************************************************************************
 * Term operations.
 *************************************************************************)

(* Options, i.e. None | Some of 'a. *)

val noneOpt_term : term
val is_noneOpt_term : term -> bool

val someOpt_term : term
val is_someOpt_term : term -> bool
val mk_someOpt_term : term -> term
val dest_someOpt_term : term -> term

(* Boolean constants. *)

val val_true_term : term
val is_val_true_term : term -> bool

val val_false_term : term
val is_val_false_term : term -> bool

(* Floating-point and integer precisions. *)

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

(* Signed / unsigned integer qualifiers. *)

val signedInt_term : term
val is_signedInt_term : term -> bool

val unsignedInt_term : term
val is_unsignedInt_term : term -> bool

(* int and rawint sets. *)

val interval_term : term
val is_interval_term : term -> bool
val mk_interval_term : term -> term -> term
val dest_interval_term : term -> term * term

val int_set_term : term
val is_int_set_term : term -> bool
val mk_int_set_term : term -> term
val dest_int_set_term : term -> term

val rawint_set_term : term
val is_rawint_set_term : term -> bool
val mk_rawint_set_term : term -> term -> term -> term
val dest_rawint_set_term : term -> term * term * term

(* Tuple classes. *)

val normalTuple_term : term
val is_normalTuple_term : term -> bool

val rawTuple_term : term
val is_rawTuple_term : term -> bool

(* Union tags. *)

val normalUnion_term : term
val is_normalUnion_term : term -> bool

val exnUnion_term : term
val is_exnUnion_term : term -> bool
