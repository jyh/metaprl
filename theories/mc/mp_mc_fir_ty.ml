(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define terms to represent FIR types and terms.
 * Specific FIR types represented here: ty, tydef.
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
declare tyPointer{ 'var; 'ty }
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
declare tyOption{ 'ty }

(* Delayed type. *)

declare tyDelayed

(* Defining types. *)

declare unionElt{ 'ty; 'bool }
declare tyDefUnion{ 'ty_var_list; 'union_type; 'elts }
declare tyDefLambda{ 'ty_var_list; 'ty }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Base types. *)

dform tyInt_df : except_mode[src] ::
   tyInt =
   `"TyInt"
dform tyEnum_df : except_mode[src] ::
   tyEnum{ 'int } =
   `"TyEnum(" slot{'int} `")"

(* Native types. *)

dform tyRawInt_df : except_mode[src] ::
   tyRawInt{ 'int_precision; 'int_signed } =
   `"TyRawInt(" slot{'int_precision} `"," slot{'int_signed} `")"
dform tyFloat_df : except_mode[src] ::
   tyFloat{ 'float_precision } =
   `"TyFloat(" slot{'float_precision} `")"

(* Functions. *)

dform tyFun_df : except_mode[src] ::
   tyFun{ 'ty_list; 'ty } =
   `"TyFun(" slot{'ty_list} `"," slot{'ty} `")"

(* Tuples. *)

dform tyUnion_df : except_mode[src] ::
   tyUnion{ 'ty_var; 'ty_list; 'int_set } =
   `"TyUnion(" slot{'ty_var} `"," slot{'ty_list} `"," slot{'int_set} `")"
dform tyTuple_df : except_mode[src] ::
   tyTuple{ 'tuple_class; 'ty_list } =
   `"TyTuple(" slot{'tuple_class} `"," slot{'ty_list} `")"
dform tyArray_df : except_mode[src] ::
   tyArray{ 'ty } =
   `"TyArray(" slot{'ty} `")"
dform tyRawData : except_mode[src] ::
   tyRawData =
   `"TyRawData"
dform tyPointer_df : except_mode[src] ::
   tyPointer{ 'var; 'ty } =
   `"TyPointer(" slot{'var} `"," slot{'ty} `")"
dform tyFrame_df : except_mode[src] ::
   tyFrame{ 'label } =
   `"TyFrame(" slot{'label} `")"

(* Polymorphism. *)

dform tyVar_df : except_mode[src] ::
   tyVar{ 'ty_var } =
   `"TyVar(" slot{'ty_var} `")"
dform tyApply_df : except_mode[src] ::
   tyApply{ 'ty_var; 'ty_list } =
   `"TyApply(" slot{'ty_var} `"," slot{'ty_list} `")"
dform tyExists_df : except_mode[src] ::
   tyExists{ 'ty_var_list; 'ty } =
   `"TyExists(" slot{'ty_var_list} `"," hspace slot{'ty} `")"
dform tyAll_df : except_mode[src] ::
   tyAll{ 'ty_var_list; 'ty } =
   `"TyAll(" slot{'ty_var_list} `"," hspace slot{'ty} `")"
dform tyProject_df : except_mode[src] ::
   tyProject{ 'var; 'num } =
   `"TyProject(" slot{'var} `"," slot{'num} `")"

(* Object-oriented. *)

dform tyCase_df : except_mode[src] ::
   tyCase{ 'ty } =
   `"TyCase(" slot{'ty} `")"
dform tyObject_df : except_mode[src] ::
   tyObject{ 'ty_var; 'ty } =
   `"TyObject(" slot{'ty_var} `"," slot{'ty} `")"
dform tyOption_df : except_mode[src] ::
   tyOption{ 'ty } =
   `"TyOption(" slot{'ty} `")"

(* Delayed type.  Type should be inferred. *)

dform tyDelayed_df : except_mode[src] ::
   tyDelayed =
   `"TyDelayed"

(* Defining types. *)

dform unionElt_df : except_mode[src] :: unionElt{ 'ty; 'bool } =
   `"(" slot{'ty} `"," slot{'bool} ")"
dform tyDefUnion_df : except_mode[src] ::
   tyDefUnion{ 'ty_var_list; 'union_ty; 'elts } =
   `"TyDefUnion(" slot{'union_ty} `"," slot{'ty_var_list} `"," slot{'elts} `")"
dform tyDefLambda_df : except_mode[src] ::
   tyDefLambda{ 'ty_var_list; 'ty } =
   `"TyDefLambda(" slot{'ty_var_list} `"," hspace slot{'ty} `")"

(*************************************************************************
 * Term operations.
 *************************************************************************)

(* Base types. *)

let tyInt_term = << tyInt >>
let tyInt_opname = opname_of_term tyInt_term
let is_tyInt_term = is_no_subterms_term tyInt_opname

let tyEnum_term = << tyEnum{ 'int } >>
let tyEnum_opname = opname_of_term tyEnum_term
let is_tyEnum_term = is_dep0_term tyEnum_opname
let mk_tyEnum_term = mk_dep0_term tyEnum_opname
let dest_tyEnum_term = dest_dep0_term tyEnum_opname

(* Native types. *)

let tyRawInt_term = << tyRawInt{ 'int_precision; 'int_signed } >>
let tyRawInt_opname = opname_of_term tyRawInt_term
let is_tyRawInt_term = is_dep0_dep0_term tyRawInt_opname
let mk_tyRawInt_term = mk_dep0_dep0_term tyRawInt_opname
let dest_tyRawInt_term = dest_dep0_dep0_term tyRawInt_opname

let tyFloat_term = << tyFloat{ 'float_precision } >>
let tyFloat_opname = opname_of_term tyFloat_term
let is_tyFloat_term = is_dep0_term tyFloat_opname
let mk_tyFloat_term = mk_dep0_term tyFloat_opname
let dest_tyFloat_term = dest_dep0_term tyFloat_opname

(* Functions. *)

let tyFun_term = << tyFun{ 'ty_list; 'ty } >>
let tyFun_opname = opname_of_term tyFun_term
let is_tyFun_term = is_dep0_dep0_term tyFun_opname
let mk_tyFun_term = mk_dep0_dep0_term tyFun_opname
let dest_tyFun_term = dest_dep0_dep0_term tyFun_opname

(* Tuples. *)

let tyUnion_term = << tyUnion{ 'ty_var; 'ty_list; 'int_set } >>
let tyUnion_opname = opname_of_term tyUnion_term
let is_tyUnion_term = is_dep0_dep0_dep0_term tyUnion_opname
let mk_tyUnion_term = mk_dep0_dep0_dep0_term tyUnion_opname
let dest_tyUnion_term = dest_dep0_dep0_dep0_term tyUnion_opname

let tyTuple_term = << tyTuple{ 'tuple_class; 'ty_list } >>
let tyTuple_opname = opname_of_term tyTuple_term
let is_tyTuple_term = is_dep0_dep0_term tyTuple_opname
let mk_tyTuple_term = mk_dep0_dep0_term tyTuple_opname
let dest_tyTuple_term = dest_dep0_dep0_term tyTuple_opname

let tyArray_term = << tyArray{ 'ty } >>
let tyArray_opname = opname_of_term tyArray_term
let is_tyArray_term = is_dep0_term tyArray_opname
let mk_tyArray_term = mk_dep0_term tyArray_opname
let dest_tyArray_term = dest_dep0_term tyArray_opname

let tyRawData_term = << tyRawData >>
let tyRawData_opname = opname_of_term tyRawData_term
let is_tyRawData_term = is_no_subterms_term tyRawData_opname

let tyPointer_term = << tyPointer{ 'var; 'ty } >>
let tyPointer_opname = opname_of_term tyPointer_term
let is_tyPointer_term = is_dep0_dep0_term tyPointer_opname
let mk_tyPointer_term = mk_dep0_dep0_term tyPointer_opname
let dest_tyPointer_term = dest_dep0_dep0_term tyPointer_opname

let tyFrame_term = << tyFrame{ 'label } >>
let tyFrame_opname = opname_of_term tyFrame_term
let is_tyFrame_term = is_dep0_term tyFrame_opname
let mk_tyFrame_term = mk_dep0_term tyFrame_opname
let dest_tyFrame_term = dest_dep0_term tyFrame_opname

(* Polymorphism. *)

let tyVar_term = << tyVar{ 'ty_var } >>
let tyVar_opname = opname_of_term tyVar_term
let is_tyVar_term = is_dep0_term tyVar_opname
let mk_tyVar_term = mk_dep0_term tyVar_opname
let dest_tyVar_term = dest_dep0_term tyVar_opname

let tyApply_term = << tyApply{ 'ty_var; 'ty_list } >>
let tyApply_opname = opname_of_term tyApply_term
let is_tyApply_term = is_dep0_dep0_term tyApply_opname
let mk_tyApply_term = mk_dep0_dep0_term tyApply_opname
let dest_tyApply_term = dest_dep0_dep0_term tyApply_opname

let tyExists_term = << tyExists{ 'ty_var_list; 'ty } >>
let tyExists_opname = opname_of_term tyExists_term
let is_tyExists_term = is_dep0_dep0_term tyExists_opname
let mk_tyExists_term = mk_dep0_dep0_term tyExists_opname
let dest_tyExists_term = dest_dep0_dep0_term tyExists_opname

let tyAll_term = << tyAll{ 'ty_var_list; 'ty } >>
let tyAll_opname = opname_of_term tyAll_term
let is_tyAll_term = is_dep0_dep0_term tyAll_opname
let mk_tyAll_term = mk_dep0_dep0_term tyAll_opname
let dest_tyAll_term = dest_dep0_dep0_term tyAll_opname

let tyProject_term = << tyProject{ 'var; 'num } >>
let tyProject_opname = opname_of_term tyProject_term
let is_tyProject_term = is_dep0_dep0_term tyProject_opname
let mk_tyProject_term = mk_dep0_dep0_term tyProject_opname
let dest_tyProject_term = dest_dep0_dep0_term tyProject_opname

(* Object-oriented. *)

let tyCase_term = << tyCase{ 'ty } >>
let tyCase_opname = opname_of_term tyCase_term
let is_tyCase_term = is_dep0_term tyCase_opname
let mk_tyCase_term = mk_dep0_term tyCase_opname
let dest_tyCase_term = dest_dep0_term tyCase_opname

let tyObject_term = << tyObject{ 'ty_var; 'ty } >>
let tyObject_opname = opname_of_term tyObject_term
let is_tyObject_term = is_dep0_dep0_term tyObject_opname
let mk_tyObject_term = mk_dep0_dep0_term tyObject_opname
let dest_tyObject_term = dest_dep0_dep0_term tyObject_opname

let tyOption_term = << tyOption{ 'ty } >>
let tyOption_opname = opname_of_term tyOption_term
let is_tyOption_term = is_dep0_term tyOption_opname
let mk_tyOption_term = mk_dep0_term tyOption_opname
let dest_tyOption_term = dest_dep0_term tyOption_opname

(* Delayed type. *)

let tyDelayed_term = << tyDelayed >>
let tyDelayed_opname = opname_of_term tyDelayed_term
let is_tyDelayed_term = is_no_subterms_term tyDelayed_opname

(* Defining types. *)

let unionElt_term = << unionElt{ 'ty; 'bool } >>
let unionElt_opname = opname_of_term unionElt_term
let is_unionElt_term = is_dep0_dep0_term unionElt_opname
let mk_unionElt_term = mk_dep0_dep0_term unionElt_opname
let dest_unionElt_term = dest_dep0_dep0_term unionElt_opname

let tyDefUnion_term = << tyDefUnion{ 'ty_var_list; 'union_type; 'elts } >>
let tyDefUnion_opname = opname_of_term tyDefUnion_term
let is_tyDefUnion_term = is_dep0_dep0_dep0_term tyDefUnion_opname
let mk_tyDefUnion_term = mk_dep0_dep0_dep0_term tyDefUnion_opname
let dest_tyDefUnion_term = dest_dep0_dep0_dep0_term tyDefUnion_opname

let tyDefLambda_term = << tyDefLambda{ 'ty_var_list; 'ty } >>
let tyDefLambda_opname = opname_of_term tyDefLambda_term
let is_tyDefLambda_term = is_dep0_dep0_term tyDefLambda_opname
let mk_tyDefLambda_term = mk_dep0_dep0_term tyDefLambda_opname
let dest_tyDefLambda_term = dest_dep0_dep0_term tyDefLambda_opname
