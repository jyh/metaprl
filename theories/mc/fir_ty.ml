(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define the types in the FIR.
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

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Integer and floating point precision. *)
declare int8
declare int16
declare int32
declare int64
declare floatSingle
declare floatDouble
declare floatLongDouble

(* Integer type. *)
declare tyInt

(* Enumeration type. *)
declare tyEnum{ 'num }

(* Native data types. *)
declare tyRawInt{ 'precision; 'sign }
declare tyFloat{ 'precision }

(* Function type. *)
declare tyFun{ 'ty_list; 'ty }

(* Tuples. *)
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

(* Delayed type. *)
declare tyDelayed

(* Union tags. *)
declare normalUnion
declare exnUnion

(* Defining types. *)
declare unionElt{ 'ty; 'bool }
declare tyDefUnion{ 'ty_var_list; 'union_ty; 'elts }
declare tyDefLambda{ 'ty_var_list; 'ty }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Integer and floating point precision. *)
dform int8_df : except_mode[src] :: int8 = `"Int8"
dform int16_df : except_mode[src] :: int16 = `"Int16"
dform int32_df : except_mode[src] :: int32 = `"Int32"
dform int64_df : except_mode[src] :: int64 = `"Int64"
dform floatSingle_df : except_mode[src] :: floatSingle = `"Single"
dform floatDouble_df : except_mode[src] :: floatDouble = `"Double"
dform floatLongDouble_df : except_mode[src] :: floatLongDouble = `"LongDouble"

(* Integer type. *)
dform tyInt_df : except_mode[src] :: tyInt = `"TyInt"

(* Enumeration type. *)
dform tyEnum_df : except_mode[src] :: tyEnum{ 'num } =
   lzone `"TyEnum(0.." slot{'num} `")" ezone

(* Native data types. *)
dform tyRawInt_df : except_mode[src] :: tyRawInt{ 'precision; 'sign } =
   `"TyRawInt(" slot{'precision} `", " slot{'sign} `")"
dform tyFloat_df : except_mode[src] :: tyFloat{ 'precision } =
   `"TyFloat(" slot{'precision} `")"

(* Function type. *)
dform tyFun_df : except_mode[src] :: tyFun{ 'ty_list; 'ty } =
   szone `"TyFun" `"(" slot{'ty_list} `" -> " slot{'ty} `")" ezone

(* Tuples. *)
dform tyUnion_df : except_mode[src] ::
   tyUnion{ 'ty_var; 'ty_list; 'int_set } =
   szone `"TyUnion(" slot{'ty_var} `", " slot{'ty_list}
   `", " slot{'int_set} `")" ezone
dform tyTuple_df : except_mode[src] :: tyTuple{ 'ty_list } =
   lzone `"TyTuple(" slot{'ty_list} `")" ezone
dform tyArray_df : except_mode[src] :: tyArray{ 'ty } =
   lzone `"TyArray(" slot{'ty} `")" ezone
dform tyRawData : except_mode[src] :: tyRawData =
   `"TyRawData"

(* Polymorphism. *)
dform tyVar_df : except_mode[src] :: tyVar{ 'ty_var } =
   `"TyVar(" slot{'ty_var} `")"
dform tyApply_df : except_mode[src] :: tyApply{ 'ty_var; 'ty_list } =
   `"TyApply(" slot{'ty_var} `", " slot{'ty_list} `")"
dform tyExists_df : except_mode[src] :: tyExists{ 'ty_var_list; 'ty } =
   `"TyExists(" slot{'ty_var_list} `", " slot{'ty} `")"
dform tyAll_df : except_mode[src] :: tyAll{ 'ty_var_list; 'ty } =
   `"TyAll(" slot{'ty_var_list} `", " slot{'ty} `")"
dform tyProject_df : except_mode[src] :: tyProject{ 'ty_var; 'num } =
   `"TyProject(" slot{'ty_var} `", " slot{'num} `")"

(* Delayed type. *)
dform tyDelayed_df : except_mode[src] :: tyDelayed = `"TyDelayed"

(* Union tags. *)
dform normalUnion_df : except_mode[src] :: normalUnion = `"NormalUnion"
dform exnUnion_df : except_mode[src] :: exnUnion = `"ExnUnion"

(* Defining types. *)
dform unionElt_df : except_mode[src] :: unionElt{ 'ty; 'bool } =
   lzone `"(" slot{'ty} `" * " slot{'bool} ")" ezone
dform tyDefUnion_df : except_mode[src] ::
   tyDefUnion{ 'ty_var_list; 'union_ty; 'elts } =
   szone `"TyDefUnion(" slot{'ty_var_list} `", " slot{'union_ty}
   `", " slot{'elts} `")" ezone
dform tyDefLambda_df : except_mode[src] :: tyDefLambda{ 'ty_var_list; 'ty } =
   szone `"TyDefLambda(" slot{'ty_var_list} `", " slot{'ty} `")" ezone
