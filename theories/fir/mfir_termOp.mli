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

open Refiner.Refiner.Term

val true_term : term
val is_true_term : term -> bool

val false_term : term
val is_false_term : term -> bool

val or_term : term
val is_or_term : term -> bool
val mk_or_term : term -> term -> term
val dest_or_term : term -> term * term

val and_term : term
val is_and_term : term -> bool
val mk_and_term : term -> term -> term
val dest_and_term : term -> term * term

val not_term : term
val is_not_term : term -> bool
val mk_not_term : term -> term
val dest_not_term : term -> term

val ifthenelse_term : term
val is_ifthenelse_term : term -> bool
val mk_ifthenelse_term : term -> term -> term -> term
val dest_ifthenelse_term : term -> term * term * term

val number_term : term
val is_number_term : term -> bool
val mk_number_term : Mp_num.num -> term
val dest_number_term : term -> Mp_num.num

val numeral_term : term
val is_numeral_term : term -> bool
val mk_numeral_term : term -> term
val dest_numeral_term : term -> term

val add_term : term
val is_add_term : term -> bool
val mk_add_term : term -> term -> term
val dest_add_term : term -> term * term

val sub_term : term
val is_sub_term : term -> bool
val mk_sub_term : term -> term -> term
val dest_sub_term : term -> term * term

val mul_term : term
val is_mul_term : term -> bool
val mk_mul_term : term -> term -> term
val dest_mul_term : term -> term * term

val div_term : term
val is_div_term : term -> bool
val mk_div_term : term -> term -> term
val dest_div_term : term -> term * term

val rem_term : term
val is_rem_term : term -> bool
val mk_rem_term : term -> term -> term
val dest_rem_term : term -> term * term

val minus_term : term
val is_minus_term : term -> bool
val mk_minus_term : term -> term
val dest_minus_term : term -> term

val int_eq_term : term
val is_int_eq_term : term -> bool
val mk_int_eq_term : term -> term -> term
val dest_int_eq_term : term -> term * term

val int_neq_term : term
val is_int_neq_term : term -> bool
val mk_int_neq_term : term -> term -> term
val dest_int_neq_term : term -> term * term

val int_lt_term : term
val is_int_lt_term : term -> bool
val mk_int_lt_term : term -> term -> term
val dest_int_lt_term : term -> term * term

val int_le_term : term
val is_int_le_term : term -> bool
val mk_int_le_term : term -> term -> term
val dest_int_le_term : term -> term * term

val int_gt_term : term
val is_int_gt_term : term -> bool
val mk_int_gt_term : term -> term -> term
val dest_int_gt_term : term -> term * term

val int_ge_term : term
val is_int_ge_term : term -> bool
val mk_int_ge_term : term -> term -> term
val dest_int_ge_term : term -> term * term

val nil_term : term
val is_nil_term : term -> bool

val cons_term : term
val is_cons_term : term -> bool
val mk_cons_term : term -> term -> term
val dest_cons_term : term -> term * term

val length_term : term
val is_length_term : term -> bool
val mk_length_term : term -> term
val dest_length_term : term -> term

val nth_elt_term : term
val is_nth_elt_term : term -> bool
val mk_nth_elt_term : term -> term -> term
val dest_nth_elt_term : term -> term * term

val interval_term : term
val is_interval_term : term -> bool
val mk_interval_term : term -> term -> term
val dest_interval_term : term -> term * term

val intset_term : term
val is_intset_term : term -> bool
val mk_intset_term : term -> term
val dest_intset_term : term -> term

val rawintset_term : term
val is_rawintset_term : term -> bool
val mk_rawintset_term : Mp_num.num -> string -> term -> term
val dest_rawintset_term : term -> Mp_num.num * string * term

val member_term : term
val is_member_term : term -> bool
val mk_member_term : term -> term -> term
val dest_member_term : term -> term * term

val subset_term : term
val is_subset_term : term -> bool
val mk_subset_term : term -> term -> term
val dest_subset_term : term -> term * term

val set_eq_term : term
val is_set_eq_term : term -> bool
val mk_set_eq_term : term -> term -> term
val dest_set_eq_term : term -> term * term

val singleton_term : term
val is_singleton_term : term -> bool
val mk_singleton_term : term -> term
val dest_singleton_term : term -> term

val intset_max_term : term
val is_intset_max_term : term -> bool

val enum_max_term : term
val is_enum_max_term : term -> bool

val rawintset_max_term : term
val is_rawintset_max_term : term -> bool
val mk_rawintset_max_term : Mp_num.num -> string -> term
val dest_rawintset_max_term : term -> Mp_num.num * string

val tyInt_term : term
val is_tyInt_term : term -> bool

val tyEnum_term : term
val is_tyEnum_term : term -> bool
val mk_tyEnum_term : Mp_num.num -> term
val dest_tyEnum_term : term -> Mp_num.num

val tyRawInt_term : term
val is_tyRawInt_term : term -> bool
val mk_tyRawInt_term : Mp_num.num -> string -> term
val dest_tyRawInt_term : term -> Mp_num.num * string

val tyFloat_term : term
val is_tyFloat_term : term -> bool
val mk_tyFloat_term : Mp_num.num -> term
val dest_tyFloat_term : term -> Mp_num.num

val tyFun_term : term
val is_tyFun_term : term -> bool
val mk_tyFun_term : term -> term -> term
val dest_tyFun_term : term -> term * term

val tyUnion_term : term
val is_tyUnion_term : term -> bool
val mk_tyUnion_term : term -> term -> term -> term
val dest_tyUnion_term : term -> term * term * term

val tyTuple_term : term
val is_tyTuple_term : term -> bool
val mk_tyTuple_term : string -> term -> term
val dest_tyTuple_term : term -> string * term

val tyArray_term : term
val is_tyArray_term : term -> bool
val mk_tyArray_term : term -> term
val dest_tyArray_term : term -> term

val tyRawData_term : term
val is_tyRawData_term : term -> bool

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
val mk_tyExists_term : string -> term -> term
val dest_tyExists_term : term -> string * term

val tyAll_term : term
val is_tyAll_term : term -> bool
val mk_tyAll_term : string -> term -> term
val dest_tyAll_term : term -> string * term

val tyProject_term : term
val is_tyProject_term : term -> bool
val mk_tyProject_term : Mp_num.num -> term -> term
val dest_tyProject_term : term -> Mp_num.num * term

val do_tyApply_term : term
val is_do_tyApply_term : term -> bool
val mk_do_tyApply_term : term -> term -> term
val dest_do_tyApply_term : term -> term * term

val tyDefPoly_term : term
val is_tyDefPoly_term : term -> bool
val mk_tyDefPoly_term : string -> term -> term
val dest_tyDefPoly_term : term -> string * term

val unionCaseElt_term : term
val is_unionCaseElt_term : term -> bool
val mk_unionCaseElt_term : term -> term -> term
val dest_unionCaseElt_term : term -> term * term

val unionCase_term : term
val is_unionCase_term : term -> bool
val mk_unionCase_term : term -> term
val dest_unionCase_term : term -> term

val tyDefUnion_term : term
val is_tyDefUnion_term : term -> bool
val mk_tyDefUnion_term : string -> term -> term
val dest_tyDefUnion_term : term -> string * term

val nth_unionCase_term : term
val is_nth_unionCase_term : term -> bool
val mk_nth_unionCase_term : term -> term -> term
val dest_nth_unionCase_term : term -> term * term

val idOp_term : term
val is_idOp_term : term -> bool

val uminusIntOp_term : term
val is_uminusIntOp_term : term -> bool

val notIntOp_term : term
val is_notIntOp_term : term -> bool

val rawBitFieldOp_term : term
val is_rawBitFieldOp_term : term -> bool
val mk_rawBitFieldOp_term : Mp_num.num -> string -> term -> term -> term
val dest_rawBitFieldOp_term : term -> Mp_num.num * string * term * term

val uminusRawIntOp_term : term
val is_uminusRawIntOp_term : term -> bool
val mk_uminusRawIntOp_term : Mp_num.num -> string -> term
val dest_uminusRawIntOp_term : term -> Mp_num.num * string

val notRawIntOp_term : term
val is_notRawIntOp_term : term -> bool
val mk_notRawIntOp_term : Mp_num.num -> string -> term
val dest_notRawIntOp_term : term -> Mp_num.num * string

val uminusFloatOp_term : term
val is_uminusFloatOp_term : term -> bool
val mk_uminusFloatOp_term : Mp_num.num -> term
val dest_uminusFloatOp_term : term -> Mp_num.num

val absFloatOp_term : term
val is_absFloatOp_term : term -> bool
val mk_absFloatOp_term : Mp_num.num -> term
val dest_absFloatOp_term : term -> Mp_num.num

val sinOp_term : term
val is_sinOp_term : term -> bool
val mk_sinOp_term : Mp_num.num -> term
val dest_sinOp_term : term -> Mp_num.num

val cosOp_term : term
val is_cosOp_term : term -> bool
val mk_cosOp_term : Mp_num.num -> term
val dest_cosOp_term : term -> Mp_num.num

val sqrtOp_term : term
val is_sqrtOp_term : term -> bool
val mk_sqrtOp_term : Mp_num.num -> term
val dest_sqrtOp_term : term -> Mp_num.num

val intOfFloatOp_term : term
val is_intOfFloatOp_term : term -> bool
val mk_intOfFloatOp_term : Mp_num.num -> term
val dest_intOfFloatOp_term : term -> Mp_num.num

val floatOfIntOp_term : term
val is_floatOfIntOp_term : term -> bool
val mk_floatOfIntOp_term : Mp_num.num -> term
val dest_floatOfIntOp_term : term -> Mp_num.num

val floatOfFloatOp_term : term
val is_floatOfFloatOp_term : term -> bool
val mk_floatOfFloatOp_term : Mp_num.num -> Mp_num.num -> term
val dest_floatOfFloatOp_term : term -> Mp_num.num * Mp_num.num

val floatOfRawIntOp_term : term
val is_floatOfRawIntOp_term : term -> bool
val mk_floatOfRawIntOp_term : Mp_num.num -> Mp_num.num -> string -> term
val dest_floatOfRawIntOp_term : term -> Mp_num.num * Mp_num.num * string

val rawIntOfIntOp_term : term
val is_rawIntOfIntOp_term : term -> bool
val mk_rawIntOfIntOp_term : Mp_num.num -> string -> term
val dest_rawIntOfIntOp_term : term -> Mp_num.num * string

val rawIntOfEnumOp_term : term
val is_rawIntOfEnumOp_term : term -> bool
val mk_rawIntOfEnumOp_term : Mp_num.num -> string -> Mp_num.num -> term
val dest_rawIntOfEnumOp_term : term -> Mp_num.num * string * Mp_num.num

val rawIntOfFloatOp_term : term
val is_rawIntOfFloatOp_term : term -> bool
val mk_rawIntOfFloatOp_term : Mp_num.num -> string -> Mp_num.num -> term
val dest_rawIntOfFloatOp_term : term -> Mp_num.num * string * Mp_num.num

val rawIntOfRawIntOp_term : term
val is_rawIntOfRawIntOp_term : term -> bool
val mk_rawIntOfRawIntOp_term : Mp_num.num -> string -> Mp_num.num -> string -> term
val dest_rawIntOfRawIntOp_term : term -> Mp_num.num * string * Mp_num.num * string

val rawIntOfPointerOp_term : term
val is_rawIntOfPointerOp_term : term -> bool
val mk_rawIntOfPointerOp_term : Mp_num.num -> string -> term
val dest_rawIntOfPointerOp_term : term -> Mp_num.num * string

val pointerOfRawIntOp_term : term
val is_pointerOfRawIntOp_term : term -> bool
val mk_pointerOfRawIntOp_term : Mp_num.num -> string -> term
val dest_pointerOfRawIntOp_term : term -> Mp_num.num * string

val andEnumOp_term : term
val is_andEnumOp_term : term -> bool
val mk_andEnumOp_term : Mp_num.num -> term
val dest_andEnumOp_term : term -> Mp_num.num

val orEnumOp_term : term
val is_orEnumOp_term : term -> bool
val mk_orEnumOp_term : Mp_num.num -> term
val dest_orEnumOp_term : term -> Mp_num.num

val xorEnumOp_term : term
val is_xorEnumOp_term : term -> bool
val mk_xorEnumOp_term : Mp_num.num -> term
val dest_xorEnumOp_term : term -> Mp_num.num

val plusIntOp_term : term
val is_plusIntOp_term : term -> bool

val minusIntOp_term : term
val is_minusIntOp_term : term -> bool

val mulIntOp_term : term
val is_mulIntOp_term : term -> bool

val divIntOp_term : term
val is_divIntOp_term : term -> bool

val remIntOp_term : term
val is_remIntOp_term : term -> bool

val lslIntOp_term : term
val is_lslIntOp_term : term -> bool

val lsrIntOp_term : term
val is_lsrIntOp_term : term -> bool

val asrIntOp_term : term
val is_asrIntOp_term : term -> bool

val andIntOp_term : term
val is_andIntOp_term : term -> bool

val orIntOp_term : term
val is_orIntOp_term : term -> bool

val xorIntOp_term : term
val is_xorIntOp_term : term -> bool

val maxIntOp_term : term
val is_maxIntOp_term : term -> bool

val minIntOp_term : term
val is_minIntOp_term : term -> bool

val eqIntOp_term : term
val is_eqIntOp_term : term -> bool

val neqIntOp_term : term
val is_neqIntOp_term : term -> bool

val ltIntOp_term : term
val is_ltIntOp_term : term -> bool

val leIntOp_term : term
val is_leIntOp_term : term -> bool

val gtIntOp_term : term
val is_gtIntOp_term : term -> bool

val geIntOp_term : term
val is_geIntOp_term : term -> bool

val cmpIntOp_term : term
val is_cmpIntOp_term : term -> bool

val plusRawIntOp_term : term
val is_plusRawIntOp_term : term -> bool
val mk_plusRawIntOp_term : Mp_num.num -> string -> term
val dest_plusRawIntOp_term : term -> Mp_num.num * string

val minusRawIntOp_term : term
val is_minusRawIntOp_term : term -> bool
val mk_minusRawIntOp_term : Mp_num.num -> string -> term
val dest_minusRawIntOp_term : term -> Mp_num.num * string

val mulRawIntOp_term : term
val is_mulRawIntOp_term : term -> bool
val mk_mulRawIntOp_term : Mp_num.num -> string -> term
val dest_mulRawIntOp_term : term -> Mp_num.num * string

val divRawIntOp_term : term
val is_divRawIntOp_term : term -> bool
val mk_divRawIntOp_term : Mp_num.num -> string -> term
val dest_divRawIntOp_term : term -> Mp_num.num * string

val remRawIntOp_term : term
val is_remRawIntOp_term : term -> bool
val mk_remRawIntOp_term : Mp_num.num -> string -> term
val dest_remRawIntOp_term : term -> Mp_num.num * string

val slRawIntOp_term : term
val is_slRawIntOp_term : term -> bool
val mk_slRawIntOp_term : Mp_num.num -> string -> term
val dest_slRawIntOp_term : term -> Mp_num.num * string

val srRawIntOp_term : term
val is_srRawIntOp_term : term -> bool
val mk_srRawIntOp_term : Mp_num.num -> string -> term
val dest_srRawIntOp_term : term -> Mp_num.num * string

val andRawIntOp_term : term
val is_andRawIntOp_term : term -> bool
val mk_andRawIntOp_term : Mp_num.num -> string -> term
val dest_andRawIntOp_term : term -> Mp_num.num * string

val orRawIntOp_term : term
val is_orRawIntOp_term : term -> bool
val mk_orRawIntOp_term : Mp_num.num -> string -> term
val dest_orRawIntOp_term : term -> Mp_num.num * string

val xorRawIntOp_term : term
val is_xorRawIntOp_term : term -> bool
val mk_xorRawIntOp_term : Mp_num.num -> string -> term
val dest_xorRawIntOp_term : term -> Mp_num.num * string

val maxRawIntOp_term : term
val is_maxRawIntOp_term : term -> bool
val mk_maxRawIntOp_term : Mp_num.num -> string -> term
val dest_maxRawIntOp_term : term -> Mp_num.num * string

val minRawIntOp_term : term
val is_minRawIntOp_term : term -> bool
val mk_minRawIntOp_term : Mp_num.num -> string -> term
val dest_minRawIntOp_term : term -> Mp_num.num * string

val rawSetBitFieldOp_term : term
val is_rawSetBitFieldOp_term : term -> bool
val mk_rawSetBitFieldOp_term : Mp_num.num -> string -> term -> term -> term
val dest_rawSetBitFieldOp_term : term -> Mp_num.num * string * term * term

val eqRawIntOp_term : term
val is_eqRawIntOp_term : term -> bool
val mk_eqRawIntOp_term : Mp_num.num -> string -> term
val dest_eqRawIntOp_term : term -> Mp_num.num * string

val neqRawIntOp_term : term
val is_neqRawIntOp_term : term -> bool
val mk_neqRawIntOp_term : Mp_num.num -> string -> term
val dest_neqRawIntOp_term : term -> Mp_num.num * string

val ltRawIntOp_term : term
val is_ltRawIntOp_term : term -> bool
val mk_ltRawIntOp_term : Mp_num.num -> string -> term
val dest_ltRawIntOp_term : term -> Mp_num.num * string

val leRawIntOp_term : term
val is_leRawIntOp_term : term -> bool
val mk_leRawIntOp_term : Mp_num.num -> string -> term
val dest_leRawIntOp_term : term -> Mp_num.num * string

val gtRawIntOp_term : term
val is_gtRawIntOp_term : term -> bool
val mk_gtRawIntOp_term : Mp_num.num -> string -> term
val dest_gtRawIntOp_term : term -> Mp_num.num * string

val geRawIntOp_term : term
val is_geRawIntOp_term : term -> bool
val mk_geRawIntOp_term : Mp_num.num -> string -> term
val dest_geRawIntOp_term : term -> Mp_num.num * string

val cmpRawIntOp_term : term
val is_cmpRawIntOp_term : term -> bool
val mk_cmpRawIntOp_term : Mp_num.num -> string -> term
val dest_cmpRawIntOp_term : term -> Mp_num.num * string

val plusFloatOp_term : term
val is_plusFloatOp_term : term -> bool
val mk_plusFloatOp_term : Mp_num.num -> term
val dest_plusFloatOp_term : term -> Mp_num.num

val minusFloatOp_term : term
val is_minusFloatOp_term : term -> bool
val mk_minusFloatOp_term : Mp_num.num -> term
val dest_minusFloatOp_term : term -> Mp_num.num

val mulFloatOp_term : term
val is_mulFloatOp_term : term -> bool
val mk_mulFloatOp_term : Mp_num.num -> term
val dest_mulFloatOp_term : term -> Mp_num.num

val divFloatOp_term : term
val is_divFloatOp_term : term -> bool
val mk_divFloatOp_term : Mp_num.num -> term
val dest_divFloatOp_term : term -> Mp_num.num

val remFloatOp_term : term
val is_remFloatOp_term : term -> bool
val mk_remFloatOp_term : Mp_num.num -> term
val dest_remFloatOp_term : term -> Mp_num.num

val maxFloatOp_term : term
val is_maxFloatOp_term : term -> bool
val mk_maxFloatOp_term : Mp_num.num -> term
val dest_maxFloatOp_term : term -> Mp_num.num

val minFloatOp_term : term
val is_minFloatOp_term : term -> bool
val mk_minFloatOp_term : Mp_num.num -> term
val dest_minFloatOp_term : term -> Mp_num.num

val eqFloatOp_term : term
val is_eqFloatOp_term : term -> bool
val mk_eqFloatOp_term : Mp_num.num -> term
val dest_eqFloatOp_term : term -> Mp_num.num

val neqFloatOp_term : term
val is_neqFloatOp_term : term -> bool
val mk_neqFloatOp_term : Mp_num.num -> term
val dest_neqFloatOp_term : term -> Mp_num.num

val ltFloatOp_term : term
val is_ltFloatOp_term : term -> bool
val mk_ltFloatOp_term : Mp_num.num -> term
val dest_ltFloatOp_term : term -> Mp_num.num

val leFloatOp_term : term
val is_leFloatOp_term : term -> bool
val mk_leFloatOp_term : Mp_num.num -> term
val dest_leFloatOp_term : term -> Mp_num.num

val gtFloatOp_term : term
val is_gtFloatOp_term : term -> bool
val mk_gtFloatOp_term : Mp_num.num -> term
val dest_gtFloatOp_term : term -> Mp_num.num

val geFloatOp_term : term
val is_geFloatOp_term : term -> bool
val mk_geFloatOp_term : Mp_num.num -> term
val dest_geFloatOp_term : term -> Mp_num.num

val cmpFloatOp_term : term
val is_cmpFloatOp_term : term -> bool
val mk_cmpFloatOp_term : Mp_num.num -> term
val dest_cmpFloatOp_term : term -> Mp_num.num

val atan2Op_term : term
val is_atan2Op_term : term -> bool
val mk_atan2Op_term : Mp_num.num -> term
val dest_atan2Op_term : term -> Mp_num.num

val eqEqOp_term : term
val is_eqEqOp_term : term -> bool

val neqEqOp_term : term
val is_neqEqOp_term : term -> bool

val atomInt_term : term
val is_atomInt_term : term -> bool
val mk_atomInt_term : term -> term
val dest_atomInt_term : term -> term

val atomEnum_term : term
val is_atomEnum_term : term -> bool
val mk_atomEnum_term : Mp_num.num -> term -> term
val dest_atomEnum_term : term -> Mp_num.num * term

val atomRawInt_term : term
val is_atomRawInt_term : term -> bool
val mk_atomRawInt_term : Mp_num.num -> string -> term -> term
val dest_atomRawInt_term : term -> Mp_num.num * string * term

val atomVar_term : term
val is_atomVar_term : term -> bool
val mk_atomVar_term : term -> term
val dest_atomVar_term : term -> term

val atomTyApply_term : term
val is_atomTyApply_term : term -> bool
val mk_atomTyApply_term : term -> term -> term -> term
val dest_atomTyApply_term : term -> term * term * term

val atomTyPack_term : term
val is_atomTyPack_term : term -> bool
val mk_atomTyPack_term : term -> term -> term -> term
val dest_atomTyPack_term : term -> term * term * term

val atomTyUnpack_term : term
val is_atomTyUnpack_term : term -> bool
val mk_atomTyUnpack_term : term -> term
val dest_atomTyUnpack_term : term -> term

val atomUnop_term : term
val is_atomUnop_term : term -> bool
val mk_atomUnop_term : term -> term -> term
val dest_atomUnop_term : term -> term * term

val atomBinop_term : term
val is_atomBinop_term : term -> bool
val mk_atomBinop_term : term -> term -> term -> term
val dest_atomBinop_term : term -> term * term * term

val allocTuple_term : term
val is_allocTuple_term : term -> bool
val mk_allocTuple_term : string -> term -> term -> term
val dest_allocTuple_term : term -> string * term * term

val allocUnion_term : term
val is_allocUnion_term : term -> bool
val mk_allocUnion_term : Mp_num.num -> term -> term -> term -> term
val dest_allocUnion_term : term -> Mp_num.num * term * term * term

val allocVArray_term : term
val is_allocVArray_term : term -> bool
val mk_allocVArray_term : term -> term -> term -> term
val dest_allocVArray_term : term -> term * term * term

val allocMalloc_term : term
val is_allocMalloc_term : term -> bool
val mk_allocMalloc_term : term -> term -> term
val dest_allocMalloc_term : term -> term * term

val letAtom_term : term
val is_letAtom_term : term -> bool
val mk_letAtom_term : term -> term -> string -> term -> term
val dest_letAtom_term : term -> term * term * string * term

val letExt_term : term
val is_letExt_term : term -> bool
val mk_letExt_term : string -> term -> term -> term -> string -> term -> term
val dest_letExt_term : term -> string * term * term * term * string * term

val tailCall_term : term
val is_tailCall_term : term -> bool
val mk_tailCall_term : term -> term -> term
val dest_tailCall_term : term -> term * term

val matchCase_term : term
val is_matchCase_term : term -> bool
val mk_matchCase_term : term -> term -> term
val dest_matchCase_term : term -> term * term

val matchExp_term : term
val is_matchExp_term : term -> bool
val mk_matchExp_term : term -> term -> term
val dest_matchExp_term : term -> term * term

val letAlloc_term : term
val is_letAlloc_term : term -> bool
val mk_letAlloc_term : term -> string -> term -> term
val dest_letAlloc_term : term -> term * string * term

val letSubscript_term : term
val is_letSubscript_term : term -> bool
val mk_letSubscript_term : term -> term -> term -> string -> term -> term
val dest_letSubscript_term : term -> term * term * term * string * term

val setSubscript_term : term
val is_setSubscript_term : term -> bool
val mk_setSubscript_term : term -> term -> term -> term -> term -> term
val dest_setSubscript_term : term -> term * term * term * term * term

val letGlobal_term : term
val is_letGlobal_term : term -> bool
val mk_letGlobal_term : term -> term -> string -> term -> term
val dest_letGlobal_term : term -> term * term * string * term

val setGlobal_term : term
val is_setGlobal_term : term -> bool
val mk_setGlobal_term : term -> term -> term -> term -> term
val dest_setGlobal_term : term -> term * term * term * term