(*
 * The Mp_mc_fir_base module defines terms to represent basic FIR
 * terms and supporting OCaml values.
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

extends Base_theory

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
declare boxedTuple
declare rawTuple

(* Union tags. *)

declare normalUnion
declare exnUnion

(*
 * Subscript operators.
 *)

(* Kind of block. *)

declare blockSub
declare rawDataSub
declare tupleSub
declare rawTupleSub

(* Kind of value. *)

declare polySub
declare rawIntSub{ 'int_precision; 'int_signed }
declare rawFloatSub{ 'float_precision }
declare pointerInfixSub
declare pointerSub
declare functionSub

(* Element width. *)

declare byteIndex
declare wordIndex

(* Kind of subscript. *)

declare intIndex
declare rawIntIndex{ 'int_precision; 'int_signed }

(* Subscripting op. *)

declare subop{ 'sub_block; 'sub_value; 'sub_index; 'sub_script }

(*
 * Tables, maps, and other structures.
 *)

(* Represent an item in a table (a value) indexed by some key. *)

declare tableItem{ 'key; 'value }

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

val boxedTuple_term : term
val is_boxedTuple_term : term -> bool

val rawTuple_term : term
val is_rawTuple_term : term -> bool

(* Union tags. *)

val normalUnion_term : term
val is_normalUnion_term : term -> bool

val exnUnion_term : term
val is_exnUnion_term : term -> bool

(*
 * Subscript operators.
 *)

(* Kind of block. *)

val blockSub_term : term
val is_blockSub_term : term -> bool

val rawDataSub_term : term
val is_rawDataSub_term : term -> bool

val tupleSub_term : term
val is_tupleSub_term : term -> bool

val rawTupleSub_term : term
val is_rawTupleSub_term : term -> bool

(* Kind of value. *)

val polySub_term : term
val is_polySub_term : term -> bool

val rawIntSub_term : term
val is_rawIntSub_term : term -> bool
val mk_rawIntSub_term : term -> term -> term
val dest_rawIntSub_term : term -> term * term

val rawFloatSub_term : term
val is_rawFloatSub_term : term -> bool
val mk_rawFloatSub_term : term -> term
val dest_rawFloatSub_term : term -> term

val pointerInfixSub_term : term
val is_pointerInfixSub_term : term -> bool

val pointerSub_term : term
val is_pointerSub_term : term -> bool

val functionSub_term : term
val is_functionSub_term : term -> bool

(* Element width. *)

val byteIndex_term : term
val is_byteIndex_term : term -> bool

val wordIndex_term : term
val is_wordIndex_term : term -> bool

(* Kind of subscript. *)

val intIndex_term : term
val is_intIndex_term : term -> bool

val rawIntIndex_term : term
val is_rawIntIndex_term : term -> bool
val mk_rawIntIndex_term : term -> term -> term
val dest_rawIntIndex_term : term -> term * term

(* Susbscripting op. *)

val subop_term : term
val is_subop_term : term -> bool
val mk_subop_term : term -> term -> term -> term -> term
val dest_subop_term : term -> term * term * term * term

(*
 * Tables, maps, and other structures.
 *)

(* Represent an item in a table (a value) indexed by some key. *)

val tableItem_term : term
val is_tableItem_term : term -> bool
val mk_tableItem_term : term -> term -> term
val dest_tableItem_term : term -> term * term
