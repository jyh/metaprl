(*
 * The Mfir_termOp module provides term construction
 * and deconstruction terms for FIR theory terms.
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
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
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

extends Mfir_basic
extends Mfir_ty
extends Mfir_exp

open Mfir_termOp_base
open Refiner.Refiner.Term

let true_term = << "true" >>
let true_opname = opname_of_term true_term
let is_true_term = is_0_dep0_term true_opname

let false_term = << "false" >>
let false_opname = opname_of_term false_term
let is_false_term = is_0_dep0_term false_opname

let or_term = << "or"{ 'bool1; 'bool2 } >>
let or_opname = opname_of_term or_term
let is_or_term = is_2_dep0_term or_opname
let mk_or_term = mk_2_dep0_term or_opname
let dest_or_term = dest_2_dep0_term or_opname

let and_term = << "and"{ 'bool1; 'bool2 } >>
let and_opname = opname_of_term and_term
let is_and_term = is_2_dep0_term and_opname
let mk_and_term = mk_2_dep0_term and_opname
let dest_and_term = dest_2_dep0_term and_opname

let not_term = << "not"{ 'boolean } >>
let not_opname = opname_of_term not_term
let is_not_term = is_1_dep0_term not_opname
let mk_not_term = mk_1_dep0_term not_opname
let dest_not_term = dest_1_dep0_term not_opname

let ifthenelse_term = << ifthenelse{ 'test; 'true_case; 'false_case } >>
let ifthenelse_opname = opname_of_term ifthenelse_term
let is_ifthenelse_term = is_3_dep0_term ifthenelse_opname
let mk_ifthenelse_term = mk_3_dep0_term ifthenelse_opname
let dest_ifthenelse_term = dest_3_dep0_term ifthenelse_opname

let number_term = << number[i:n] >>
let number_opname = opname_of_term number_term
let is_number_term = is_num_0_dep0_term number_opname
let mk_number_term = mk_num_0_dep0_term number_opname
let dest_number_term = dest_num_0_dep0_term number_opname

let numeral_term = << numeral{ 'num } >>
let numeral_opname = opname_of_term numeral_term
let is_numeral_term = is_1_dep0_term numeral_opname
let mk_numeral_term = mk_1_dep0_term numeral_opname
let dest_numeral_term = dest_1_dep0_term numeral_opname

let add_term = << add{ 'num1; 'num2 } >>
let add_opname = opname_of_term add_term
let is_add_term = is_2_dep0_term add_opname
let mk_add_term = mk_2_dep0_term add_opname
let dest_add_term = dest_2_dep0_term add_opname

let sub_term = << sub{ 'num1; 'num2 } >>
let sub_opname = opname_of_term sub_term
let is_sub_term = is_2_dep0_term sub_opname
let mk_sub_term = mk_2_dep0_term sub_opname
let dest_sub_term = dest_2_dep0_term sub_opname

let mul_term = << mul{ 'num1; 'num2 } >>
let mul_opname = opname_of_term mul_term
let is_mul_term = is_2_dep0_term mul_opname
let mk_mul_term = mk_2_dep0_term mul_opname
let dest_mul_term = dest_2_dep0_term mul_opname

let div_term = << div{ 'num1; 'num2 } >>
let div_opname = opname_of_term div_term
let is_div_term = is_2_dep0_term div_opname
let mk_div_term = mk_2_dep0_term div_opname
let dest_div_term = dest_2_dep0_term div_opname

let rem_term = << rem{ 'num1; 'num2 } >>
let rem_opname = opname_of_term rem_term
let is_rem_term = is_2_dep0_term rem_opname
let mk_rem_term = mk_2_dep0_term rem_opname
let dest_rem_term = dest_2_dep0_term rem_opname

let minus_term = << minus{ 'num } >>
let minus_opname = opname_of_term minus_term
let is_minus_term = is_1_dep0_term minus_opname
let mk_minus_term = mk_1_dep0_term minus_opname
let dest_minus_term = dest_1_dep0_term minus_opname

let int_eq_term = << int_eq{ 'num1; 'num2 } >>
let int_eq_opname = opname_of_term int_eq_term
let is_int_eq_term = is_2_dep0_term int_eq_opname
let mk_int_eq_term = mk_2_dep0_term int_eq_opname
let dest_int_eq_term = dest_2_dep0_term int_eq_opname

let int_neq_term = << int_neq{ 'num1; 'num2 } >>
let int_neq_opname = opname_of_term int_neq_term
let is_int_neq_term = is_2_dep0_term int_neq_opname
let mk_int_neq_term = mk_2_dep0_term int_neq_opname
let dest_int_neq_term = dest_2_dep0_term int_neq_opname

let int_lt_term = << int_lt{ 'num1; 'num2 } >>
let int_lt_opname = opname_of_term int_lt_term
let is_int_lt_term = is_2_dep0_term int_lt_opname
let mk_int_lt_term = mk_2_dep0_term int_lt_opname
let dest_int_lt_term = dest_2_dep0_term int_lt_opname

let int_le_term = << int_le{ 'num1; 'num2 } >>
let int_le_opname = opname_of_term int_le_term
let is_int_le_term = is_2_dep0_term int_le_opname
let mk_int_le_term = mk_2_dep0_term int_le_opname
let dest_int_le_term = dest_2_dep0_term int_le_opname

let int_gt_term = << int_gt{ 'num1; 'num2 } >>
let int_gt_opname = opname_of_term int_gt_term
let is_int_gt_term = is_2_dep0_term int_gt_opname
let mk_int_gt_term = mk_2_dep0_term int_gt_opname
let dest_int_gt_term = dest_2_dep0_term int_gt_opname

let int_ge_term = << int_ge{ 'num1; 'num2 } >>
let int_ge_opname = opname_of_term int_ge_term
let is_int_ge_term = is_2_dep0_term int_ge_opname
let mk_int_ge_term = mk_2_dep0_term int_ge_opname
let dest_int_ge_term = dest_2_dep0_term int_ge_opname

let nil_term = << nil >>
let nil_opname = opname_of_term nil_term
let is_nil_term = is_0_dep0_term nil_opname

let cons_term = << cons{ 'elt; 'tail } >>
let cons_opname = opname_of_term cons_term
let is_cons_term = is_2_dep0_term cons_opname
let mk_cons_term = mk_2_dep0_term cons_opname
let dest_cons_term = dest_2_dep0_term cons_opname

let interval_term = << interval{ 'left; 'right } >>
let interval_opname = opname_of_term interval_term
let is_interval_term = is_2_dep0_term interval_opname
let mk_interval_term = mk_2_dep0_term interval_opname
let dest_interval_term = dest_2_dep0_term interval_opname

let intset_term = << intset{ 'interval_list } >>
let intset_opname = opname_of_term intset_term
let is_intset_term = is_1_dep0_term intset_opname
let mk_intset_term = mk_1_dep0_term intset_opname
let dest_intset_term = dest_1_dep0_term intset_opname

let rawintset_term = << rawintset[precision:n, sign:s]{ 'interval_list } >>
let rawintset_opname = opname_of_term rawintset_term
let is_rawintset_term = is_num_str_1_dep0_term rawintset_opname
let mk_rawintset_term = mk_num_str_1_dep0_term rawintset_opname
let dest_rawintset_term = dest_num_str_1_dep0_term rawintset_opname

let member_term = << member{ 'num; 'set } >>
let member_opname = opname_of_term member_term
let is_member_term = is_2_dep0_term member_opname
let mk_member_term = mk_2_dep0_term member_opname
let dest_member_term = dest_2_dep0_term member_opname

let singleton_term = << singleton{ 'i } >>
let singleton_opname = opname_of_term singleton_term
let is_singleton_term = is_1_dep0_term singleton_opname
let mk_singleton_term = mk_1_dep0_term singleton_opname
let dest_singleton_term = dest_1_dep0_term singleton_opname

let intset_max_term = << intset_max >>
let intset_max_opname = opname_of_term intset_max_term
let is_intset_max_term = is_0_dep0_term intset_max_opname

let enum_max_term = << enum_max >>
let enum_max_opname = opname_of_term enum_max_term
let is_enum_max_term = is_0_dep0_term enum_max_opname

let rawintset_max_term = << rawintset_max[precision:n, sign:s] >>
let rawintset_max_opname = opname_of_term rawintset_max_term
let is_rawintset_max_term = is_num_str_0_dep0_term rawintset_max_opname
let mk_rawintset_max_term = mk_num_str_0_dep0_term rawintset_max_opname
let dest_rawintset_max_term = dest_num_str_0_dep0_term rawintset_max_opname

let tyInt_term = << tyInt >>
let tyInt_opname = opname_of_term tyInt_term
let is_tyInt_term = is_0_dep0_term tyInt_opname

let tyEnum_term = << tyEnum[i:n] >>
let tyEnum_opname = opname_of_term tyEnum_term
let is_tyEnum_term = is_num_0_dep0_term tyEnum_opname
let mk_tyEnum_term = mk_num_0_dep0_term tyEnum_opname
let dest_tyEnum_term = dest_num_0_dep0_term tyEnum_opname

let tyRawInt_term = << tyRawInt[precision:n, sign:s] >>
let tyRawInt_opname = opname_of_term tyRawInt_term
let is_tyRawInt_term = is_num_str_0_dep0_term tyRawInt_opname
let mk_tyRawInt_term = mk_num_str_0_dep0_term tyRawInt_opname
let dest_tyRawInt_term = dest_num_str_0_dep0_term tyRawInt_opname

let tyFloat_term = << tyFloat[precision:n] >>
let tyFloat_opname = opname_of_term tyFloat_term
let is_tyFloat_term = is_num_0_dep0_term tyFloat_opname
let mk_tyFloat_term = mk_num_0_dep0_term tyFloat_opname
let dest_tyFloat_term = dest_num_0_dep0_term tyFloat_opname

let tyFun_term = << tyFun{ 'arg_type; 'res_type } >>
let tyFun_opname = opname_of_term tyFun_term
let is_tyFun_term = is_2_dep0_term tyFun_opname
let mk_tyFun_term = mk_2_dep0_term tyFun_opname
let dest_tyFun_term = dest_2_dep0_term tyFun_opname

let tyUnion_term = << tyUnion{ 'ty_var; 'ty_list; 'intset } >>
let tyUnion_opname = opname_of_term tyUnion_term
let is_tyUnion_term = is_3_dep0_term tyUnion_opname
let mk_tyUnion_term = mk_3_dep0_term tyUnion_opname
let dest_tyUnion_term = dest_3_dep0_term tyUnion_opname

let tyTuple_term = << tyTuple[tc:s]{ 'ty_list } >>
let tyTuple_opname = opname_of_term tyTuple_term
let is_tyTuple_term = is_str_1_dep0_term tyTuple_opname
let mk_tyTuple_term = mk_str_1_dep0_term tyTuple_opname
let dest_tyTuple_term = dest_str_1_dep0_term tyTuple_opname

let tyArray_term = << tyArray{ 'ty } >>
let tyArray_opname = opname_of_term tyArray_term
let is_tyArray_term = is_1_dep0_term tyArray_opname
let mk_tyArray_term = mk_1_dep0_term tyArray_opname
let dest_tyArray_term = dest_1_dep0_term tyArray_opname

let tyRawData_term = << tyRawData >>
let tyRawData_opname = opname_of_term tyRawData_term
let is_tyRawData_term = is_0_dep0_term tyRawData_opname

let tyVar_term = << tyVar{ 'ty_var } >>
let tyVar_opname = opname_of_term tyVar_term
let is_tyVar_term = is_1_dep0_term tyVar_opname
let mk_tyVar_term = mk_1_dep0_term tyVar_opname
let dest_tyVar_term = dest_1_dep0_term tyVar_opname

let tyApply_term = << tyApply{ 'ty_var; 'ty_list } >>
let tyApply_opname = opname_of_term tyApply_term
let is_tyApply_term = is_2_dep0_term tyApply_opname
let mk_tyApply_term = mk_2_dep0_term tyApply_opname
let dest_tyApply_term = dest_2_dep0_term tyApply_opname

let tyExists_term = << tyExists{ t. 'ty['t] } >>
let tyExists_opname = opname_of_term tyExists_term
let is_tyExists_term = is_0_dep0_1_dep1_term tyExists_opname
let mk_tyExists_term = mk_0_dep0_1_dep1_term tyExists_opname
let dest_tyExists_term = dest_0_dep0_1_dep1_term tyExists_opname

let tyAll_term = << tyAll{ t. 'ty['t] } >>
let tyAll_opname = opname_of_term tyAll_term
let is_tyAll_term = is_0_dep0_1_dep1_term tyAll_opname
let mk_tyAll_term = mk_0_dep0_1_dep1_term tyAll_opname
let dest_tyAll_term = dest_0_dep0_1_dep1_term tyAll_opname

let tyProject_term = << tyProject[i:n]{ 'var } >>
let tyProject_opname = opname_of_term tyProject_term
let is_tyProject_term = is_num_1_dep0_term tyProject_opname
let mk_tyProject_term = mk_num_1_dep0_term tyProject_opname
let dest_tyProject_term = dest_num_1_dep0_term tyProject_opname

let tyDefPoly_term = << tyDefPoly{ t. 'ty['t] } >>
let tyDefPoly_opname = opname_of_term tyDefPoly_term
let is_tyDefPoly_term = is_0_dep0_1_dep1_term tyDefPoly_opname
let mk_tyDefPoly_term = mk_0_dep0_1_dep1_term tyDefPoly_opname
let dest_tyDefPoly_term = dest_0_dep0_1_dep1_term tyDefPoly_opname

let unionCaseElt_term = << unionCaseElt{ 'ty; 'boolean } >>
let unionCaseElt_opname = opname_of_term unionCaseElt_term
let is_unionCaseElt_term = is_2_dep0_term unionCaseElt_opname
let mk_unionCaseElt_term = mk_2_dep0_term unionCaseElt_opname
let dest_unionCaseElt_term = dest_2_dep0_term unionCaseElt_opname

let unionCase_term = << unionCase{ 'elts } >>
let unionCase_opname = opname_of_term unionCase_term
let is_unionCase_term = is_1_dep0_term unionCase_opname
let mk_unionCase_term = mk_1_dep0_term unionCase_opname
let dest_unionCase_term = dest_1_dep0_term unionCase_opname

let tyDefUnion_term = << tyDefUnion[str:s]{ 'cases } >>
let tyDefUnion_opname = opname_of_term tyDefUnion_term
let is_tyDefUnion_term = is_str_1_dep0_term tyDefUnion_opname
let mk_tyDefUnion_term = mk_str_1_dep0_term tyDefUnion_opname
let dest_tyDefUnion_term = dest_str_1_dep0_term tyDefUnion_opname

let idOp_term = << idOp >>
let idOp_opname = opname_of_term idOp_term
let is_idOp_term = is_0_dep0_term idOp_opname

let uminusIntOp_term = << uminusIntOp >>
let uminusIntOp_opname = opname_of_term uminusIntOp_term
let is_uminusIntOp_term = is_0_dep0_term uminusIntOp_opname

let notIntOp_term = << notIntOp >>
let notIntOp_opname = opname_of_term notIntOp_term
let is_notIntOp_term = is_0_dep0_term notIntOp_opname

let rawBitFieldOp_term = << rawBitFieldOp[precision:n, sign:s]{ 'num1; 'num2 } >>
let rawBitFieldOp_opname = opname_of_term rawBitFieldOp_term
let is_rawBitFieldOp_term = is_num_str_2_dep0_term rawBitFieldOp_opname
let mk_rawBitFieldOp_term = mk_num_str_2_dep0_term rawBitFieldOp_opname
let dest_rawBitFieldOp_term = dest_num_str_2_dep0_term rawBitFieldOp_opname

let uminusRawIntOp_term = << uminusRawIntOp[precision:n, sign:s] >>
let uminusRawIntOp_opname = opname_of_term uminusRawIntOp_term
let is_uminusRawIntOp_term = is_num_str_0_dep0_term uminusRawIntOp_opname
let mk_uminusRawIntOp_term = mk_num_str_0_dep0_term uminusRawIntOp_opname
let dest_uminusRawIntOp_term = dest_num_str_0_dep0_term uminusRawIntOp_opname

let notRawIntOp_term = << notRawIntOp[precision:n, sign:s] >>
let notRawIntOp_opname = opname_of_term notRawIntOp_term
let is_notRawIntOp_term = is_num_str_0_dep0_term notRawIntOp_opname
let mk_notRawIntOp_term = mk_num_str_0_dep0_term notRawIntOp_opname
let dest_notRawIntOp_term = dest_num_str_0_dep0_term notRawIntOp_opname

let uminusFloatOp_term = << uminusFloatOp[precision:n] >>
let uminusFloatOp_opname = opname_of_term uminusFloatOp_term
let is_uminusFloatOp_term = is_num_0_dep0_term uminusFloatOp_opname
let mk_uminusFloatOp_term = mk_num_0_dep0_term uminusFloatOp_opname
let dest_uminusFloatOp_term = dest_num_0_dep0_term uminusFloatOp_opname

let absFloatOp_term = << absFloatOp[precision:n] >>
let absFloatOp_opname = opname_of_term absFloatOp_term
let is_absFloatOp_term = is_num_0_dep0_term absFloatOp_opname
let mk_absFloatOp_term = mk_num_0_dep0_term absFloatOp_opname
let dest_absFloatOp_term = dest_num_0_dep0_term absFloatOp_opname

let sinOp_term = << sinOp[precision:n] >>
let sinOp_opname = opname_of_term sinOp_term
let is_sinOp_term = is_num_0_dep0_term sinOp_opname
let mk_sinOp_term = mk_num_0_dep0_term sinOp_opname
let dest_sinOp_term = dest_num_0_dep0_term sinOp_opname

let cosOp_term = << cosOp[precision:n] >>
let cosOp_opname = opname_of_term cosOp_term
let is_cosOp_term = is_num_0_dep0_term cosOp_opname
let mk_cosOp_term = mk_num_0_dep0_term cosOp_opname
let dest_cosOp_term = dest_num_0_dep0_term cosOp_opname

let sqrtOp_term = << sqrtOp[precision:n] >>
let sqrtOp_opname = opname_of_term sqrtOp_term
let is_sqrtOp_term = is_num_0_dep0_term sqrtOp_opname
let mk_sqrtOp_term = mk_num_0_dep0_term sqrtOp_opname
let dest_sqrtOp_term = dest_num_0_dep0_term sqrtOp_opname

let intOfFloatOp_term = << intOfFloatOp[precision:n] >>
let intOfFloatOp_opname = opname_of_term intOfFloatOp_term
let is_intOfFloatOp_term = is_num_0_dep0_term intOfFloatOp_opname
let mk_intOfFloatOp_term = mk_num_0_dep0_term intOfFloatOp_opname
let dest_intOfFloatOp_term = dest_num_0_dep0_term intOfFloatOp_opname

let floatOfIntOp_term = << floatOfIntOp[precision:n] >>
let floatOfIntOp_opname = opname_of_term floatOfIntOp_term
let is_floatOfIntOp_term = is_num_0_dep0_term floatOfIntOp_opname
let mk_floatOfIntOp_term = mk_num_0_dep0_term floatOfIntOp_opname
let dest_floatOfIntOp_term = dest_num_0_dep0_term floatOfIntOp_opname

let floatOfFloatOp_term = << floatOfFloatOp[dest_prec:n, src_prec:n] >>
let floatOfFloatOp_opname = opname_of_term floatOfFloatOp_term
let is_floatOfFloatOp_term = is_num_num_0_dep0_term floatOfFloatOp_opname
let mk_floatOfFloatOp_term = mk_num_num_0_dep0_term floatOfFloatOp_opname
let dest_floatOfFloatOp_term = dest_num_num_0_dep0_term floatOfFloatOp_opname

let floatOfRawIntOp_term = << floatOfRawIntOp[float_prec:n, int_prec:n, int_sign:s] >>
let floatOfRawIntOp_opname = opname_of_term floatOfRawIntOp_term
let is_floatOfRawIntOp_term = is_num_num_str_0_dep0_term floatOfRawIntOp_opname
let mk_floatOfRawIntOp_term = mk_num_num_str_0_dep0_term floatOfRawIntOp_opname
let dest_floatOfRawIntOp_term = dest_num_num_str_0_dep0_term floatOfRawIntOp_opname

let rawIntOfIntOp_term = << rawIntOfIntOp[precision:n, sign:s] >>
let rawIntOfIntOp_opname = opname_of_term rawIntOfIntOp_term
let is_rawIntOfIntOp_term = is_num_str_0_dep0_term rawIntOfIntOp_opname
let mk_rawIntOfIntOp_term = mk_num_str_0_dep0_term rawIntOfIntOp_opname
let dest_rawIntOfIntOp_term = dest_num_str_0_dep0_term rawIntOfIntOp_opname

let rawIntOfEnumOp_term = << rawIntOfEnumOp[precision:n, sign:s, i:n] >>
let rawIntOfEnumOp_opname = opname_of_term rawIntOfEnumOp_term
let is_rawIntOfEnumOp_term = is_num_str_num_0_dep0_term rawIntOfEnumOp_opname
let mk_rawIntOfEnumOp_term = mk_num_str_num_0_dep0_term rawIntOfEnumOp_opname
let dest_rawIntOfEnumOp_term = dest_num_str_num_0_dep0_term rawIntOfEnumOp_opname

let rawIntOfFloatOp_term = << rawIntOfFloatOp[int_prec:n, int_sign:s, float_prec:n] >>
let rawIntOfFloatOp_opname = opname_of_term rawIntOfFloatOp_term
let is_rawIntOfFloatOp_term = is_num_str_num_0_dep0_term rawIntOfFloatOp_opname
let mk_rawIntOfFloatOp_term = mk_num_str_num_0_dep0_term rawIntOfFloatOp_opname
let dest_rawIntOfFloatOp_term = dest_num_str_num_0_dep0_term rawIntOfFloatOp_opname

let rawIntOfRawIntOp_term = << rawIntOfRawIntOp[dest_prec:n, dest_sign:s, src_prec:n, src_sign:s] >>
let rawIntOfRawIntOp_opname = opname_of_term rawIntOfRawIntOp_term
let is_rawIntOfRawIntOp_term = is_num_str_num_str_0_dep0_term rawIntOfRawIntOp_opname
let mk_rawIntOfRawIntOp_term = mk_num_str_num_str_0_dep0_term rawIntOfRawIntOp_opname
let dest_rawIntOfRawIntOp_term = dest_num_str_num_str_0_dep0_term rawIntOfRawIntOp_opname

let rawIntOfPointerOp_term = << rawIntOfPointerOp[precision:n, sign:s] >>
let rawIntOfPointerOp_opname = opname_of_term rawIntOfPointerOp_term
let is_rawIntOfPointerOp_term = is_num_str_0_dep0_term rawIntOfPointerOp_opname
let mk_rawIntOfPointerOp_term = mk_num_str_0_dep0_term rawIntOfPointerOp_opname
let dest_rawIntOfPointerOp_term = dest_num_str_0_dep0_term rawIntOfPointerOp_opname

let pointerOfRawIntOp_term = << pointerOfRawIntOp[precision:n, sign:s] >>
let pointerOfRawIntOp_opname = opname_of_term pointerOfRawIntOp_term
let is_pointerOfRawIntOp_term = is_num_str_0_dep0_term pointerOfRawIntOp_opname
let mk_pointerOfRawIntOp_term = mk_num_str_0_dep0_term pointerOfRawIntOp_opname
let dest_pointerOfRawIntOp_term = dest_num_str_0_dep0_term pointerOfRawIntOp_opname

let andEnumOp_term = << andEnumOp[i:n] >>
let andEnumOp_opname = opname_of_term andEnumOp_term
let is_andEnumOp_term = is_num_0_dep0_term andEnumOp_opname
let mk_andEnumOp_term = mk_num_0_dep0_term andEnumOp_opname
let dest_andEnumOp_term = dest_num_0_dep0_term andEnumOp_opname

let orEnumOp_term = << orEnumOp[i:n] >>
let orEnumOp_opname = opname_of_term orEnumOp_term
let is_orEnumOp_term = is_num_0_dep0_term orEnumOp_opname
let mk_orEnumOp_term = mk_num_0_dep0_term orEnumOp_opname
let dest_orEnumOp_term = dest_num_0_dep0_term orEnumOp_opname

let xorEnumOp_term = << xorEnumOp[i:n] >>
let xorEnumOp_opname = opname_of_term xorEnumOp_term
let is_xorEnumOp_term = is_num_0_dep0_term xorEnumOp_opname
let mk_xorEnumOp_term = mk_num_0_dep0_term xorEnumOp_opname
let dest_xorEnumOp_term = dest_num_0_dep0_term xorEnumOp_opname

let plusIntOp_term = << plusIntOp >>
let plusIntOp_opname = opname_of_term plusIntOp_term
let is_plusIntOp_term = is_0_dep0_term plusIntOp_opname

let minusIntOp_term = << minusIntOp >>
let minusIntOp_opname = opname_of_term minusIntOp_term
let is_minusIntOp_term = is_0_dep0_term minusIntOp_opname

let mulIntOp_term = << mulIntOp >>
let mulIntOp_opname = opname_of_term mulIntOp_term
let is_mulIntOp_term = is_0_dep0_term mulIntOp_opname

let divIntOp_term = << divIntOp >>
let divIntOp_opname = opname_of_term divIntOp_term
let is_divIntOp_term = is_0_dep0_term divIntOp_opname

let remIntOp_term = << remIntOp >>
let remIntOp_opname = opname_of_term remIntOp_term
let is_remIntOp_term = is_0_dep0_term remIntOp_opname

let lslIntOp_term = << lslIntOp >>
let lslIntOp_opname = opname_of_term lslIntOp_term
let is_lslIntOp_term = is_0_dep0_term lslIntOp_opname

let lsrIntOp_term = << lsrIntOp >>
let lsrIntOp_opname = opname_of_term lsrIntOp_term
let is_lsrIntOp_term = is_0_dep0_term lsrIntOp_opname

let asrIntOp_term = << asrIntOp >>
let asrIntOp_opname = opname_of_term asrIntOp_term
let is_asrIntOp_term = is_0_dep0_term asrIntOp_opname

let andIntOp_term = << andIntOp >>
let andIntOp_opname = opname_of_term andIntOp_term
let is_andIntOp_term = is_0_dep0_term andIntOp_opname

let orIntOp_term = << orIntOp >>
let orIntOp_opname = opname_of_term orIntOp_term
let is_orIntOp_term = is_0_dep0_term orIntOp_opname

let xorIntOp_term = << xorIntOp >>
let xorIntOp_opname = opname_of_term xorIntOp_term
let is_xorIntOp_term = is_0_dep0_term xorIntOp_opname

let maxIntOp_term = << maxIntOp >>
let maxIntOp_opname = opname_of_term maxIntOp_term
let is_maxIntOp_term = is_0_dep0_term maxIntOp_opname

let minIntOp_term = << minIntOp >>
let minIntOp_opname = opname_of_term minIntOp_term
let is_minIntOp_term = is_0_dep0_term minIntOp_opname

let eqIntOp_term = << eqIntOp >>
let eqIntOp_opname = opname_of_term eqIntOp_term
let is_eqIntOp_term = is_0_dep0_term eqIntOp_opname

let neqIntOp_term = << neqIntOp >>
let neqIntOp_opname = opname_of_term neqIntOp_term
let is_neqIntOp_term = is_0_dep0_term neqIntOp_opname

let ltIntOp_term = << ltIntOp >>
let ltIntOp_opname = opname_of_term ltIntOp_term
let is_ltIntOp_term = is_0_dep0_term ltIntOp_opname

let leIntOp_term = << leIntOp >>
let leIntOp_opname = opname_of_term leIntOp_term
let is_leIntOp_term = is_0_dep0_term leIntOp_opname

let gtIntOp_term = << gtIntOp >>
let gtIntOp_opname = opname_of_term gtIntOp_term
let is_gtIntOp_term = is_0_dep0_term gtIntOp_opname

let geIntOp_term = << geIntOp >>
let geIntOp_opname = opname_of_term geIntOp_term
let is_geIntOp_term = is_0_dep0_term geIntOp_opname

let cmpIntOp_term = << cmpIntOp >>
let cmpIntOp_opname = opname_of_term cmpIntOp_term
let is_cmpIntOp_term = is_0_dep0_term cmpIntOp_opname

let plusRawIntOp_term = << plusRawIntOp[precision:n, sign:s] >>
let plusRawIntOp_opname = opname_of_term plusRawIntOp_term
let is_plusRawIntOp_term = is_num_str_0_dep0_term plusRawIntOp_opname
let mk_plusRawIntOp_term = mk_num_str_0_dep0_term plusRawIntOp_opname
let dest_plusRawIntOp_term = dest_num_str_0_dep0_term plusRawIntOp_opname

let minusRawIntOp_term = << minusRawIntOp[precision:n, sign:s] >>
let minusRawIntOp_opname = opname_of_term minusRawIntOp_term
let is_minusRawIntOp_term = is_num_str_0_dep0_term minusRawIntOp_opname
let mk_minusRawIntOp_term = mk_num_str_0_dep0_term minusRawIntOp_opname
let dest_minusRawIntOp_term = dest_num_str_0_dep0_term minusRawIntOp_opname

let mulRawIntOp_term = << mulRawIntOp[precision:n, sign:s] >>
let mulRawIntOp_opname = opname_of_term mulRawIntOp_term
let is_mulRawIntOp_term = is_num_str_0_dep0_term mulRawIntOp_opname
let mk_mulRawIntOp_term = mk_num_str_0_dep0_term mulRawIntOp_opname
let dest_mulRawIntOp_term = dest_num_str_0_dep0_term mulRawIntOp_opname

let divRawIntOp_term = << divRawIntOp[precision:n, sign:s] >>
let divRawIntOp_opname = opname_of_term divRawIntOp_term
let is_divRawIntOp_term = is_num_str_0_dep0_term divRawIntOp_opname
let mk_divRawIntOp_term = mk_num_str_0_dep0_term divRawIntOp_opname
let dest_divRawIntOp_term = dest_num_str_0_dep0_term divRawIntOp_opname

let remRawIntOp_term = << remRawIntOp[precision:n, sign:s] >>
let remRawIntOp_opname = opname_of_term remRawIntOp_term
let is_remRawIntOp_term = is_num_str_0_dep0_term remRawIntOp_opname
let mk_remRawIntOp_term = mk_num_str_0_dep0_term remRawIntOp_opname
let dest_remRawIntOp_term = dest_num_str_0_dep0_term remRawIntOp_opname

let slRawIntOp_term = << slRawIntOp[precision:n, sign:s] >>
let slRawIntOp_opname = opname_of_term slRawIntOp_term
let is_slRawIntOp_term = is_num_str_0_dep0_term slRawIntOp_opname
let mk_slRawIntOp_term = mk_num_str_0_dep0_term slRawIntOp_opname
let dest_slRawIntOp_term = dest_num_str_0_dep0_term slRawIntOp_opname

let srRawIntOp_term = << srRawIntOp[precision:n, sign:s] >>
let srRawIntOp_opname = opname_of_term srRawIntOp_term
let is_srRawIntOp_term = is_num_str_0_dep0_term srRawIntOp_opname
let mk_srRawIntOp_term = mk_num_str_0_dep0_term srRawIntOp_opname
let dest_srRawIntOp_term = dest_num_str_0_dep0_term srRawIntOp_opname

let andRawIntOp_term = << andRawIntOp[precision:n, sign:s] >>
let andRawIntOp_opname = opname_of_term andRawIntOp_term
let is_andRawIntOp_term = is_num_str_0_dep0_term andRawIntOp_opname
let mk_andRawIntOp_term = mk_num_str_0_dep0_term andRawIntOp_opname
let dest_andRawIntOp_term = dest_num_str_0_dep0_term andRawIntOp_opname

let orRawIntOp_term = << orRawIntOp[precision:n, sign:s] >>
let orRawIntOp_opname = opname_of_term orRawIntOp_term
let is_orRawIntOp_term = is_num_str_0_dep0_term orRawIntOp_opname
let mk_orRawIntOp_term = mk_num_str_0_dep0_term orRawIntOp_opname
let dest_orRawIntOp_term = dest_num_str_0_dep0_term orRawIntOp_opname

let xorRawIntOp_term = << xorRawIntOp[precision:n, sign:s] >>
let xorRawIntOp_opname = opname_of_term xorRawIntOp_term
let is_xorRawIntOp_term = is_num_str_0_dep0_term xorRawIntOp_opname
let mk_xorRawIntOp_term = mk_num_str_0_dep0_term xorRawIntOp_opname
let dest_xorRawIntOp_term = dest_num_str_0_dep0_term xorRawIntOp_opname

let maxRawIntOp_term = << maxRawIntOp[precision:n, sign:s] >>
let maxRawIntOp_opname = opname_of_term maxRawIntOp_term
let is_maxRawIntOp_term = is_num_str_0_dep0_term maxRawIntOp_opname
let mk_maxRawIntOp_term = mk_num_str_0_dep0_term maxRawIntOp_opname
let dest_maxRawIntOp_term = dest_num_str_0_dep0_term maxRawIntOp_opname

let minRawIntOp_term = << minRawIntOp[precision:n, sign:s] >>
let minRawIntOp_opname = opname_of_term minRawIntOp_term
let is_minRawIntOp_term = is_num_str_0_dep0_term minRawIntOp_opname
let mk_minRawIntOp_term = mk_num_str_0_dep0_term minRawIntOp_opname
let dest_minRawIntOp_term = dest_num_str_0_dep0_term minRawIntOp_opname

let rawSetBitFieldOp_term = << rawSetBitFieldOp[precision:n, sign:s]{ 'num1; 'num2 } >>
let rawSetBitFieldOp_opname = opname_of_term rawSetBitFieldOp_term
let is_rawSetBitFieldOp_term = is_num_str_2_dep0_term rawSetBitFieldOp_opname
let mk_rawSetBitFieldOp_term = mk_num_str_2_dep0_term rawSetBitFieldOp_opname
let dest_rawSetBitFieldOp_term = dest_num_str_2_dep0_term rawSetBitFieldOp_opname

let eqRawIntOp_term = << eqRawIntOp[precision:n, sign:s] >>
let eqRawIntOp_opname = opname_of_term eqRawIntOp_term
let is_eqRawIntOp_term = is_num_str_0_dep0_term eqRawIntOp_opname
let mk_eqRawIntOp_term = mk_num_str_0_dep0_term eqRawIntOp_opname
let dest_eqRawIntOp_term = dest_num_str_0_dep0_term eqRawIntOp_opname

let neqRawIntOp_term = << neqRawIntOp[precision:n, sign:s] >>
let neqRawIntOp_opname = opname_of_term neqRawIntOp_term
let is_neqRawIntOp_term = is_num_str_0_dep0_term neqRawIntOp_opname
let mk_neqRawIntOp_term = mk_num_str_0_dep0_term neqRawIntOp_opname
let dest_neqRawIntOp_term = dest_num_str_0_dep0_term neqRawIntOp_opname

let ltRawIntOp_term = << ltRawIntOp[precision:n, sign:s] >>
let ltRawIntOp_opname = opname_of_term ltRawIntOp_term
let is_ltRawIntOp_term = is_num_str_0_dep0_term ltRawIntOp_opname
let mk_ltRawIntOp_term = mk_num_str_0_dep0_term ltRawIntOp_opname
let dest_ltRawIntOp_term = dest_num_str_0_dep0_term ltRawIntOp_opname

let leRawIntOp_term = << leRawIntOp[precision:n, sign:s] >>
let leRawIntOp_opname = opname_of_term leRawIntOp_term
let is_leRawIntOp_term = is_num_str_0_dep0_term leRawIntOp_opname
let mk_leRawIntOp_term = mk_num_str_0_dep0_term leRawIntOp_opname
let dest_leRawIntOp_term = dest_num_str_0_dep0_term leRawIntOp_opname

let gtRawIntOp_term = << gtRawIntOp[precision:n, sign:s] >>
let gtRawIntOp_opname = opname_of_term gtRawIntOp_term
let is_gtRawIntOp_term = is_num_str_0_dep0_term gtRawIntOp_opname
let mk_gtRawIntOp_term = mk_num_str_0_dep0_term gtRawIntOp_opname
let dest_gtRawIntOp_term = dest_num_str_0_dep0_term gtRawIntOp_opname

let geRawIntOp_term = << geRawIntOp[precision:n, sign:s] >>
let geRawIntOp_opname = opname_of_term geRawIntOp_term
let is_geRawIntOp_term = is_num_str_0_dep0_term geRawIntOp_opname
let mk_geRawIntOp_term = mk_num_str_0_dep0_term geRawIntOp_opname
let dest_geRawIntOp_term = dest_num_str_0_dep0_term geRawIntOp_opname

let cmpRawIntOp_term = << cmpRawIntOp[precision:n, sign:s] >>
let cmpRawIntOp_opname = opname_of_term cmpRawIntOp_term
let is_cmpRawIntOp_term = is_num_str_0_dep0_term cmpRawIntOp_opname
let mk_cmpRawIntOp_term = mk_num_str_0_dep0_term cmpRawIntOp_opname
let dest_cmpRawIntOp_term = dest_num_str_0_dep0_term cmpRawIntOp_opname

let plusFloatOp_term = << plusFloatOp[precision:n] >>
let plusFloatOp_opname = opname_of_term plusFloatOp_term
let is_plusFloatOp_term = is_num_0_dep0_term plusFloatOp_opname
let mk_plusFloatOp_term = mk_num_0_dep0_term plusFloatOp_opname
let dest_plusFloatOp_term = dest_num_0_dep0_term plusFloatOp_opname

let minusFloatOp_term = << minusFloatOp[precision:n] >>
let minusFloatOp_opname = opname_of_term minusFloatOp_term
let is_minusFloatOp_term = is_num_0_dep0_term minusFloatOp_opname
let mk_minusFloatOp_term = mk_num_0_dep0_term minusFloatOp_opname
let dest_minusFloatOp_term = dest_num_0_dep0_term minusFloatOp_opname

let mulFloatOp_term = << mulFloatOp[precision:n] >>
let mulFloatOp_opname = opname_of_term mulFloatOp_term
let is_mulFloatOp_term = is_num_0_dep0_term mulFloatOp_opname
let mk_mulFloatOp_term = mk_num_0_dep0_term mulFloatOp_opname
let dest_mulFloatOp_term = dest_num_0_dep0_term mulFloatOp_opname

let divFloatOp_term = << divFloatOp[precision:n] >>
let divFloatOp_opname = opname_of_term divFloatOp_term
let is_divFloatOp_term = is_num_0_dep0_term divFloatOp_opname
let mk_divFloatOp_term = mk_num_0_dep0_term divFloatOp_opname
let dest_divFloatOp_term = dest_num_0_dep0_term divFloatOp_opname

let remFloatOp_term = << remFloatOp[precision:n] >>
let remFloatOp_opname = opname_of_term remFloatOp_term
let is_remFloatOp_term = is_num_0_dep0_term remFloatOp_opname
let mk_remFloatOp_term = mk_num_0_dep0_term remFloatOp_opname
let dest_remFloatOp_term = dest_num_0_dep0_term remFloatOp_opname

let maxFloatOp_term = << maxFloatOp[precision:n] >>
let maxFloatOp_opname = opname_of_term maxFloatOp_term
let is_maxFloatOp_term = is_num_0_dep0_term maxFloatOp_opname
let mk_maxFloatOp_term = mk_num_0_dep0_term maxFloatOp_opname
let dest_maxFloatOp_term = dest_num_0_dep0_term maxFloatOp_opname

let minFloatOp_term = << minFloatOp[precision:n] >>
let minFloatOp_opname = opname_of_term minFloatOp_term
let is_minFloatOp_term = is_num_0_dep0_term minFloatOp_opname
let mk_minFloatOp_term = mk_num_0_dep0_term minFloatOp_opname
let dest_minFloatOp_term = dest_num_0_dep0_term minFloatOp_opname

let eqFloatOp_term = << eqFloatOp[precision:n] >>
let eqFloatOp_opname = opname_of_term eqFloatOp_term
let is_eqFloatOp_term = is_num_0_dep0_term eqFloatOp_opname
let mk_eqFloatOp_term = mk_num_0_dep0_term eqFloatOp_opname
let dest_eqFloatOp_term = dest_num_0_dep0_term eqFloatOp_opname

let neqFloatOp_term = << neqFloatOp[precision:n] >>
let neqFloatOp_opname = opname_of_term neqFloatOp_term
let is_neqFloatOp_term = is_num_0_dep0_term neqFloatOp_opname
let mk_neqFloatOp_term = mk_num_0_dep0_term neqFloatOp_opname
let dest_neqFloatOp_term = dest_num_0_dep0_term neqFloatOp_opname

let ltFloatOp_term = << ltFloatOp[precision:n] >>
let ltFloatOp_opname = opname_of_term ltFloatOp_term
let is_ltFloatOp_term = is_num_0_dep0_term ltFloatOp_opname
let mk_ltFloatOp_term = mk_num_0_dep0_term ltFloatOp_opname
let dest_ltFloatOp_term = dest_num_0_dep0_term ltFloatOp_opname

let leFloatOp_term = << leFloatOp[precision:n] >>
let leFloatOp_opname = opname_of_term leFloatOp_term
let is_leFloatOp_term = is_num_0_dep0_term leFloatOp_opname
let mk_leFloatOp_term = mk_num_0_dep0_term leFloatOp_opname
let dest_leFloatOp_term = dest_num_0_dep0_term leFloatOp_opname

let gtFloatOp_term = << gtFloatOp[precision:n] >>
let gtFloatOp_opname = opname_of_term gtFloatOp_term
let is_gtFloatOp_term = is_num_0_dep0_term gtFloatOp_opname
let mk_gtFloatOp_term = mk_num_0_dep0_term gtFloatOp_opname
let dest_gtFloatOp_term = dest_num_0_dep0_term gtFloatOp_opname

let geFloatOp_term = << geFloatOp[precision:n] >>
let geFloatOp_opname = opname_of_term geFloatOp_term
let is_geFloatOp_term = is_num_0_dep0_term geFloatOp_opname
let mk_geFloatOp_term = mk_num_0_dep0_term geFloatOp_opname
let dest_geFloatOp_term = dest_num_0_dep0_term geFloatOp_opname

let cmpFloatOp_term = << cmpFloatOp[precision:n] >>
let cmpFloatOp_opname = opname_of_term cmpFloatOp_term
let is_cmpFloatOp_term = is_num_0_dep0_term cmpFloatOp_opname
let mk_cmpFloatOp_term = mk_num_0_dep0_term cmpFloatOp_opname
let dest_cmpFloatOp_term = dest_num_0_dep0_term cmpFloatOp_opname

let atan2Op_term = << atan2Op[precision:n] >>
let atan2Op_opname = opname_of_term atan2Op_term
let is_atan2Op_term = is_num_0_dep0_term atan2Op_opname
let mk_atan2Op_term = mk_num_0_dep0_term atan2Op_opname
let dest_atan2Op_term = dest_num_0_dep0_term atan2Op_opname

let eqEqOp_term = << eqEqOp >>
let eqEqOp_opname = opname_of_term eqEqOp_term
let is_eqEqOp_term = is_0_dep0_term eqEqOp_opname

let neqEqOp_term = << neqEqOp >>
let neqEqOp_opname = opname_of_term neqEqOp_term
let is_neqEqOp_term = is_0_dep0_term neqEqOp_opname

let atomInt_term = << atomInt{ 'num } >>
let atomInt_opname = opname_of_term atomInt_term
let is_atomInt_term = is_1_dep0_term atomInt_opname
let mk_atomInt_term = mk_1_dep0_term atomInt_opname
let dest_atomInt_term = dest_1_dep0_term atomInt_opname

let atomEnum_term = << atomEnum[bound:n]{ 'num } >>
let atomEnum_opname = opname_of_term atomEnum_term
let is_atomEnum_term = is_num_1_dep0_term atomEnum_opname
let mk_atomEnum_term = mk_num_1_dep0_term atomEnum_opname
let dest_atomEnum_term = dest_num_1_dep0_term atomEnum_opname

let atomRawInt_term = << atomRawInt[precision:n, sign:s]{ 'num } >>
let atomRawInt_opname = opname_of_term atomRawInt_term
let is_atomRawInt_term = is_num_str_1_dep0_term atomRawInt_opname
let mk_atomRawInt_term = mk_num_str_1_dep0_term atomRawInt_opname
let dest_atomRawInt_term = dest_num_str_1_dep0_term atomRawInt_opname

let atomVar_term = << atomVar{ 'var } >>
let atomVar_opname = opname_of_term atomVar_term
let is_atomVar_term = is_1_dep0_term atomVar_opname
let mk_atomVar_term = mk_1_dep0_term atomVar_opname
let dest_atomVar_term = dest_1_dep0_term atomVar_opname

let atomTyApply_term = << atomTyApply{ 'atom; 'ty; 'ty_list } >>
let atomTyApply_opname = opname_of_term atomTyApply_term
let is_atomTyApply_term = is_3_dep0_term atomTyApply_opname
let mk_atomTyApply_term = mk_3_dep0_term atomTyApply_opname
let dest_atomTyApply_term = dest_3_dep0_term atomTyApply_opname

let atomTyPack_term = << atomTyPack{ 'var; 'ty; 'ty_list } >>
let atomTyPack_opname = opname_of_term atomTyPack_term
let is_atomTyPack_term = is_3_dep0_term atomTyPack_opname
let mk_atomTyPack_term = mk_3_dep0_term atomTyPack_opname
let dest_atomTyPack_term = dest_3_dep0_term atomTyPack_opname

let atomTyUnpack_term = << atomTyUnpack{ 'var } >>
let atomTyUnpack_opname = opname_of_term atomTyUnpack_term
let is_atomTyUnpack_term = is_1_dep0_term atomTyUnpack_opname
let mk_atomTyUnpack_term = mk_1_dep0_term atomTyUnpack_opname
let dest_atomTyUnpack_term = dest_1_dep0_term atomTyUnpack_opname

let atomUnop_term = << atomUnop{ 'unop; 'atom } >>
let atomUnop_opname = opname_of_term atomUnop_term
let is_atomUnop_term = is_2_dep0_term atomUnop_opname
let mk_atomUnop_term = mk_2_dep0_term atomUnop_opname
let dest_atomUnop_term = dest_2_dep0_term atomUnop_opname

let atomBinop_term = << atomBinop{ 'binop; 'atom1; 'atom2 } >>
let atomBinop_opname = opname_of_term atomBinop_term
let is_atomBinop_term = is_3_dep0_term atomBinop_opname
let mk_atomBinop_term = mk_3_dep0_term atomBinop_opname
let dest_atomBinop_term = dest_3_dep0_term atomBinop_opname

let allocTuple_term = << allocTuple[tc:s]{ 'ty; 'atom_list } >>
let allocTuple_opname = opname_of_term allocTuple_term
let is_allocTuple_term = is_str_2_dep0_term allocTuple_opname
let mk_allocTuple_term = mk_str_2_dep0_term allocTuple_opname
let dest_allocTuple_term = dest_str_2_dep0_term allocTuple_opname

let allocUnion_term = << allocUnion[case:n]{ 'ty; 'ty_var; 'atom_list } >>
let allocUnion_opname = opname_of_term allocUnion_term
let is_allocUnion_term = is_num_3_dep0_term allocUnion_opname
let mk_allocUnion_term = mk_num_3_dep0_term allocUnion_opname
let dest_allocUnion_term = dest_num_3_dep0_term allocUnion_opname

let allocVArray_term = << allocVArray{ 'ty; 'atom1; 'atom2 } >>
let allocVArray_opname = opname_of_term allocVArray_term
let is_allocVArray_term = is_3_dep0_term allocVArray_opname
let mk_allocVArray_term = mk_3_dep0_term allocVArray_opname
let dest_allocVArray_term = dest_3_dep0_term allocVArray_opname

let allocMalloc_term = << allocMalloc{ 'ty; 'atom } >>
let allocMalloc_opname = opname_of_term allocMalloc_term
let is_allocMalloc_term = is_2_dep0_term allocMalloc_opname
let mk_allocMalloc_term = mk_2_dep0_term allocMalloc_opname
let dest_allocMalloc_term = dest_2_dep0_term allocMalloc_opname

let letAtom_term = << letAtom{ 'ty; 'atom; var. 'exp['var] } >>
let letAtom_opname = opname_of_term letAtom_term
let is_letAtom_term = is_2_dep0_1_dep1_term letAtom_opname
let mk_letAtom_term = mk_2_dep0_1_dep1_term letAtom_opname
let dest_letAtom_term = dest_2_dep0_1_dep1_term letAtom_opname

let letExt_term = << letExt[str:s]{ 'fun_res_type; 'fun_arg_types; 'fun_args; v. 'exp['v] } >>
let letExt_opname = opname_of_term letExt_term
let is_letExt_term = is_str_3_dep0_1_dep1_term letExt_opname
let mk_letExt_term = mk_str_3_dep0_1_dep1_term letExt_opname
let dest_letExt_term = dest_str_3_dep0_1_dep1_term letExt_opname

let tailCall_term = << tailCall{ 'atom; 'atom_list } >>
let tailCall_opname = opname_of_term tailCall_term
let is_tailCall_term = is_2_dep0_term tailCall_opname
let mk_tailCall_term = mk_2_dep0_term tailCall_opname
let dest_tailCall_term = dest_2_dep0_term tailCall_opname

let matchCase_term = << matchCase{ 'set; 'exp } >>
let matchCase_opname = opname_of_term matchCase_term
let is_matchCase_term = is_2_dep0_term matchCase_opname
let mk_matchCase_term = mk_2_dep0_term matchCase_opname
let dest_matchCase_term = dest_2_dep0_term matchCase_opname

let matchExp_term = << matchExp{ 'atom; 'matchCase_list } >>
let matchExp_opname = opname_of_term matchExp_term
let is_matchExp_term = is_2_dep0_term matchExp_opname
let mk_matchExp_term = mk_2_dep0_term matchExp_opname
let dest_matchExp_term = dest_2_dep0_term matchExp_opname

let letAlloc_term = << letAlloc{ 'alloc_op; v. 'exp['v] } >>
let letAlloc_opname = opname_of_term letAlloc_term
let is_letAlloc_term = is_1_dep0_1_dep1_term letAlloc_opname
let mk_letAlloc_term = mk_1_dep0_1_dep1_term letAlloc_opname
let dest_letAlloc_term = dest_1_dep0_1_dep1_term letAlloc_opname

let letSubscript_term = << letSubscript{ 'ty; 'atom1; 'atom2; v. 'exp['v] } >>
let letSubscript_opname = opname_of_term letSubscript_term
let is_letSubscript_term = is_3_dep0_1_dep1_term letSubscript_opname
let mk_letSubscript_term = mk_3_dep0_1_dep1_term letSubscript_opname
let dest_letSubscript_term = dest_3_dep0_1_dep1_term letSubscript_opname

let setSubscript_term = << setSubscript{ 'atom1; 'atom2; 'ty; 'atom3; 'exp } >>
let setSubscript_opname = opname_of_term setSubscript_term
let is_setSubscript_term = is_5_dep0_term setSubscript_opname
let mk_setSubscript_term = mk_5_dep0_term setSubscript_opname
let dest_setSubscript_term = dest_5_dep0_term setSubscript_opname

let letGlobal_term = << letGlobal{ 'ty; 'label; v. 'exp['v] } >>
let letGlobal_opname = opname_of_term letGlobal_term
let is_letGlobal_term = is_2_dep0_1_dep1_term letGlobal_opname
let mk_letGlobal_term = mk_2_dep0_1_dep1_term letGlobal_opname
let dest_letGlobal_term = dest_2_dep0_1_dep1_term letGlobal_opname

let setGlobal_term = << setGlobal{ 'label; 'ty; 'atom; 'exp } >>
let setGlobal_opname = opname_of_term setGlobal_term
let is_setGlobal_term = is_4_dep0_term setGlobal_opname
let mk_setGlobal_term = mk_4_dep0_term setGlobal_opname
let dest_setGlobal_term = dest_4_dep0_term setGlobal_opname