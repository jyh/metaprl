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
open Refiner.Refiner.TermOp

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
 * Term declarations.
 *************************************************************************)

(* Options, i.e. None | Some of 'a. *)

dform noneOpt_df : except_mode[src] ::
   noneOpt =
   `"NoneOpt"
dform someOpt_df : except_mode[src] ::
   someOpt{ 'a } =
   `"SomeOpt(" slot{'a} `")"

(* Boolean constants. *)

dform val_true_df : except_mode[src] ::
   val_true =
   `"Val_True"
dform val_false_df : except_mode[src] ::
   val_false =
   `"Val_False"

(* Floating-point and integer precisions. *)

dform int8_df : except_mode[src] ::
   int8 =
   `"Int8"
dform int16_df : except_mode[src] ::
   int16 =
   `"Int16"
dform int32_df : except_mode[src] ::
   int32 =
   `"Int32"
dform int64_df : except_mode[src] ::
   int64 =
   `"Int64"
dform floatSingle_df : except_mode[src] ::
   floatSingle =
   `"Single"
dform floatDouble_df : except_mode[src] ::
   floatDouble =
   `"Double"
dform floatLongDouble_df : except_mode[src] ::
   floatLongDouble =
   `"LongDouble"

(* Signed / unsigned integer qualifiers. *)

dform signedInt_df : except_mode[src] ::
   signedInt =
   `"SignedInt"
dform unsignedInt_df : except_mode[src] ::
   unsignedInt =
   `"UnsignedInt"

(* int and rawint sets. *)

dform interval_df : except_mode[src] ::
   interval{ 'left; 'right } =
   `"Interval(" slot{'left} `"," slot{'right} `")"
dform int_set_df : except_mode[src] ::
   int_set{ 'interval_list } =
   `"Int_set(" slot{'interval_list} `")"
dform rawint_set_df : except_mode[src] ::
   rawint_set{ 'int_precision; 'int_signed; 'interval_list } =
   `"Rawint_set(" slot{'int_precision} `"," slot{'int_signed} `","
   slot{'interval_list} `")"

(* Tuple classes. *)

dform normalTuple_df : except_mode[src] ::
   normalTuple =
   `"NormalTuple"
dform rawTuple_df : except_mode[src] ::
   rawTuple =
   `"RawTuple"

(* Union tags. *)

dform normalUnion_df : except_mode[src] ::
   normalUnion =
   `"NormalUnion"
dform exnUnion_df : except_mode[src] ::
   exnUnion =
   `"ExnUnion"

(*************************************************************************
 * Term operations.
 *************************************************************************)

(* Options, i.e. None | Some of 'a. *)

let noneOpt_term = << noneOpt >>
let noneOpt_opname = opname_of_term noneOpt_term
let is_noneOpt_term = is_no_subterms_term noneOpt_opname

let someOpt_term = << someOpt{ 'a } >>
let someOpt_opname = opname_of_term someOpt_term
let is_someOpt_term = is_dep0_term someOpt_opname
let mk_someOpt_term = mk_dep0_term someOpt_opname
let dest_someOpt_term = dest_dep0_term someOpt_opname

(* Boolean constants. *)

let val_true_term = << val_true >>
let val_true_opname = opname_of_term val_true_term
let is_val_true_term = is_no_subterms_term val_true_opname

let val_false_term = << val_false >>
let val_false_opname = opname_of_term val_false_term
let is_val_false_term = is_no_subterms_term val_false_opname

(* Floating-point and integer precisions. *)

let int8_term = << int8 >>
let int8_opname = opname_of_term int8_term
let is_int8_term = is_no_subterms_term int8_opname

let int16_term = << int16 >>
let int16_opname = opname_of_term int16_term
let is_int16_term = is_no_subterms_term int16_opname

let int32_term = << int32 >>
let int32_opname = opname_of_term int32_term
let is_int32_term = is_no_subterms_term int32_opname

let int64_term = << int64 >>
let int64_opname = opname_of_term int64_term
let is_int64_term = is_no_subterms_term int64_opname

let floatSingle_term = << floatSingle >>
let floatSingle_opname = opname_of_term floatSingle_term
let is_floatSingle_term = is_no_subterms_term floatSingle_opname

let floatDouble_term = << floatDouble >>
let floatDouble_opname = opname_of_term floatDouble_term
let is_floatDouble_term = is_no_subterms_term floatDouble_opname

let floatLongDouble_term = << floatLongDouble >>
let floatLongDouble_opname = opname_of_term floatLongDouble_term
let is_floatLongDouble_term = is_no_subterms_term floatLongDouble_opname

(* Signed / unsigned integer qualifiers. *)

let signedInt_term = << signedInt >>
let signedInt_opname = opname_of_term signedInt_term
let is_signedInt_term = is_no_subterms_term signedInt_opname

let unsignedInt_term = << unsignedInt >>
let unsignedInt_opname = opname_of_term unsignedInt_term
let is_unsignedInt_term = is_no_subterms_term unsignedInt_opname

(* int and rawint sets. *)

let interval_term = << interval{ 'left; 'right } >>
let interval_opname = opname_of_term interval_term
let is_interval_term = is_dep0_dep0_term interval_opname
let mk_interval_term = mk_dep0_dep0_term interval_opname
let dest_interval_term = dest_dep0_dep0_term interval_opname

let int_set_term = << int_set{ 'interval_list } >>
let int_set_opname = opname_of_term int_set_term
let is_int_set_term = is_dep0_term int_set_opname
let mk_int_set_term = mk_dep0_term int_set_opname
let dest_int_set_term = dest_dep0_term int_set_opname

let rawint_set_term =
   << rawint_set{ 'int_precision; 'int_signed; 'interval_list } >>
let rawint_set_opname = opname_of_term rawint_set_term
let is_rawint_set_term = is_dep0_dep0_dep0_term rawint_set_opname
let mk_rawint_set_term = mk_dep0_dep0_dep0_term rawint_set_opname
let dest_rawint_set_term = dest_dep0_dep0_dep0_term rawint_set_opname

(* Tuple classes *)

let normalTuple_term = << normalTuple >>
let normalTuple_opname = opname_of_term normalTuple_term
let is_normalTuple_term = is_no_subterms_term normalTuple_opname

let rawTuple_term = << rawTuple >>
let rawTuple_opname = opname_of_term rawTuple_term
let is_rawTuple_term = is_no_subterms_term rawTuple_opname

(* Union tags. *)

let normalUnion_term = << normalUnion >>
let normalUnion_opname = opname_of_term normalUnion_term
let is_normalUnion_term = is_no_subterms_term normalUnion_opname

let exnUnion_term = << exnUnion >>
let exnUnion_opname = opname_of_term exnUnion_term
let is_exnUnion_term = is_no_subterms_term exnUnion_opname
