(*!
 * @begin[doc]
 * @theory[Mp_mc_fir_base]
 *
 * The @tt{Mp_mc_fir_base} module defines terms to represent basic FIR
 * terms and supporting @OCaml values.
 * @end[doc].
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * @email{emre@its.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Base_theory
(*! @docoff *)

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Mp_mc_base

(*************************************************************************
 * Term declarations.
 *************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * @tt{noneOpt} and @tt{someOpt} represent @OCaml option
 * values, in other words, values of the type @tt{'a option}.
 * @tt{Some v} is represented as @tt{someOpt@{v@}}.
 * @end[doc]
 *)

declare noneOpt
declare someOpt{ 'a }

(*!
 * @begin[doc]
 *
 * @tt{val_true} and @tt{val_false} represent the @OCaml
 * boolean constants @tt{true} and @tt{false}.  Within the FIR,
 * true and false are actually represented as
 * @hrefterm[atomEnum]s (see @hreftheory[Mp_mc_fir_eval]).
 * @end[doc]
 *)
declare val_true
declare val_false

(*!
 * @begin[doc]
 *
 * The FIR has support for integer and floating point types of
 * various precisions (see @hrefterm[tyRawInt] and @hrefterm[tyFloat]
 * in @hreftheory[Mp_mc_fir_ty]).  The following seven terms specifiy
 * 8-bit, 16-bit, 32-bit, and 64-bit integer precision as well as
 * single precision (4 byte), double precision (8 byte), and
 * long double (10 byte) precision floats.  By convention,
 * subterms called @tt{int_precision} and @tt{float_precision}
 * refer to one of these terms.
 * @end[doc]
 *)

declare int8
declare int16
declare int32
declare int64
declare floatSingle
declare floatDouble
declare floatLongDouble

(*!
 * @begin[doc]
 *
 * @hrefterm[tyRawInt] also requires information about whether
 * the integer type is signed or unsigned, which is what the following
 * two terms specify.  By convention, subterms called @tt{int_signed}
 * refer to one of these terms.
 * @end[doc]
 *)

declare signedInt
declare unsignedInt

(*!
 * @begin[doc]
 *
 * The FIR has support for basic integer (@hrefterm[tyInt])
 * and raw-intger (@hrefterm[tyRawInt]) sets.  @tt{int_set} and
 * @tt{rawint_set} encode sets as a list (see @hreftheory[Itt_list])
 * of closed @tt{interval}s.  Each @tt{interval} has subterms for
 * the left and right bounds, which should be @hrefterm[number]s.
 * @tt{rawint_set}s also require subterms to encode the precision
 * and signing of the @hrefterm[tyRawInt]s.  It is assumed that each
 * bound in the list has the same precision and signing.
 * @end[doc]
 *)

declare interval{ 'left; 'right } (* closed bounds, i.e. [left, right] *)
declare int_set{ 'interval_list }
declare rawint_set{ 'int_precision; 'int_signed; 'interval_list }

(*!
 * @begin[doc]
 *
 * Tuple classes. (Documentation incomplete.)
 * @end[doc]
 *)

declare normalTuple
declare rawTuple


(*!
 * @begin[doc]
 *
 * Union types. (Documentation incomplete.)
 * @end[doc]
 *)

declare normalUnion
declare exnUnion

(*!
 * @begin[doc]
 *
 * Subscript operators. (Documentation incomplete.)
 * @end[doc]
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

(*!
 * @begin[doc]
 *
 * Tables, maps, and other structures.
 * @end[doc]
 *)

(* Represent an item in a table (a value) indexed by some key. *)

declare tableItem{ 'key; 'value }

(*! @docoff *)

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

(*
 * Subscript operators.
 *)

(* Kind of block. *)

dform blockSub_df : except_mode[src] ::
   blockSub =
   `"BlockSub"
dform rawDataSub_df : except_mode[src] ::
   rawDataSub =
   `"RawDataSub"
dform tupleSub_df : except_mode[src] ::
   tupleSub =
   `"TupleSub"
dform rawTupleSub_df : except_mode[src] ::
   rawTupleSub =
   `"RawTupleSub"

(* Kind of value. *)

dform polySub_df : except_mode[src] ::
   polySub =
   `"PolySub"
dform rawIntSub_df : except_mode[src] ::
   rawIntSub{ 'int_precision; 'int_signed } =
   `"RawIntSub(" slot{'int_precision} `"," slot{'int_signed}
dform rawFloatSub_df : except_mode[src] ::
   rawFloatSub{ 'float_precision } =
   `"RawFloatSub(" slot{'float_precision} `")"
dform pointerInfixSUb_df : except_mode[src] ::
   pointerInfixSub =
   `"PointerInfixSub"
dform pointerSub_df : except_mode[src] ::
   pointerSub =
   `"PointerSub"
dform functionSub_df : except_mode[src] ::
   functionSub =
   `"FunctionSub"

(* Element width. *)

dform byteIndex_df : except_mode[src] ::
   byteIndex =
   `"ByteIndex"
dform wordIndex_df : except_mode[src] ::
   wordIndex =
   `"WordIndex"

(* Kind of subscript. *)

dform intIndex_df : except_mode[src] ::
   intIndex =
   `"IntIndex"
dform rawIntIndex_df : except_mode[src] ::
   rawIntIndex{ 'int_precision; 'int_signed } =
   `"RawIntIndex(" slot{'int_precision} `"," slot{'int_signed} `")"

(* Subscripting op. *)

dform subop_df : except_mode[src] ::
   subop{ 'sub_block; 'sub_value; 'sub_index; 'sub_script } =
   `"Subop(" slot{'sub_block} `"," slot{'sub_value} `","
   slot{'sub_index} `"," slot{'sub_script} `")"

(*
 * Tables, maps, and other structures.
 *)

(* Represent an item in a table (a value) indexed by some key. *)

dform tableItem_df : except_mode[src] ::
   tableItem{ 'key; 'value } =
   `"TableItem(" slot{'key} `"," slot{'value} `")"

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

(*
 * Subscript operators.
 *)

(* Kind of block. *)

let blockSub_term = << blockSub >>
let blockSub_opname = opname_of_term blockSub_term
let is_blockSub_term = is_no_subterms_term blockSub_opname

let rawDataSub_term = << rawDataSub >>
let rawDataSub_opname = opname_of_term rawDataSub_term
let is_rawDataSub_term = is_no_subterms_term rawDataSub_opname

let tupleSub_term = << tupleSub >>
let tupleSub_opname = opname_of_term tupleSub_term
let is_tupleSub_term = is_no_subterms_term tupleSub_opname

let rawTupleSub_term = << rawTupleSub >>
let rawTupleSub_opname = opname_of_term rawTupleSub_term
let is_rawTupleSub_term = is_no_subterms_term rawTupleSub_opname

(* Kind of value. *)

let polySub_term = << polySub >>
let polySub_opname = opname_of_term polySub_term
let is_polySub_term = is_no_subterms_term polySub_opname

let rawIntSub_term = << rawIntSub{ 'int_precision; 'int_signed } >>
let rawIntSub_opname = opname_of_term rawIntSub_term
let is_rawIntSub_term = is_dep0_dep0_term rawIntSub_opname
let mk_rawIntSub_term = mk_dep0_dep0_term rawIntSub_opname
let dest_rawIntSub_term = dest_dep0_dep0_term rawIntSub_opname

let rawFloatSub_term = << rawFloatSub{ 'float_precision } >>
let rawFloatSub_opname = opname_of_term rawFloatSub_term
let is_rawFloatSub_term = is_dep0_term rawFloatSub_opname
let mk_rawFloatSub_term = mk_dep0_term rawFloatSub_opname
let dest_rawFloatSub_term = dest_dep0_term rawFloatSub_opname

let pointerInfixSub_term = << pointerInfixSub >>
let pointerInfixSub_opname = opname_of_term pointerInfixSub_term
let is_pointerInfixSub_term = is_no_subterms_term pointerInfixSub_opname

let pointerSub_term = << pointerSub >>
let pointerSub_opname = opname_of_term pointerSub_term
let is_pointerSub_term = is_no_subterms_term pointerSub_opname

let functionSub_term = << functionSub >>
let functionSub_opname = opname_of_term functionSub_term
let is_functionSub_term = is_no_subterms_term functionSub_opname

(* Element width. *)

let byteIndex_term = << byteIndex >>
let byteIndex_opname = opname_of_term byteIndex_term
let is_byteIndex_term = is_no_subterms_term byteIndex_opname

let wordIndex_term = << wordIndex >>
let wordIndex_opname = opname_of_term wordIndex_term
let is_wordIndex_term = is_no_subterms_term wordIndex_opname

(* Kind of subscript. *)

let intIndex_term = << intIndex >>
let intIndex_opname = opname_of_term intIndex_term
let is_intIndex_term = is_no_subterms_term intIndex_opname

let rawIntIndex_term = << rawIntIndex{ 'int_precision; 'int_signed } >>
let rawIntIndex_opname = opname_of_term rawIntIndex_term
let is_rawIntIndex_term = is_dep0_dep0_term rawIntIndex_opname
let mk_rawIntIndex_term = mk_dep0_dep0_term rawIntIndex_opname
let dest_rawIntIndex_term = dest_dep0_dep0_term rawIntIndex_opname

(* Subscripting op. *)

let subop_term = << subop{ 'sub_block; 'sub_value; 'sub_index; 'sub_script } >>
let subop_opname = opname_of_term subop_term
let is_subop_term = is_4_dep0_term subop_opname
let mk_subop_term = mk_4_dep0_term subop_opname
let dest_subop_term = dest_4_dep0_term subop_opname

(*
 * Tables, maps, and other structures.
 *)

(* Represent an item in a table (a value) indexed by some key. *)

let tableItem_term = << tableItem{ 'key; 'value } >>
let tableItem_opname = opname_of_term tableItem_term
let is_tableItem_term = is_dep0_dep0_term tableItem_opname
let mk_tableItem_term = mk_dep0_dep0_term tableItem_opname
let dest_tableItem_term = dest_dep0_dep0_term tableItem_opname
