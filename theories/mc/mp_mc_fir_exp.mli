(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define terms to represent FIR types and terms.
 * Specific FIR types represented here: unop, binop, sub_block, sub_value,
 * sub_index, sub_script, atom, alloc_op, tailop, pred_nop, pred_unop,
 * pred_binop, pred, debug_line, debug_vars, debug_info, exp.
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
 * Declarations.
 *************************************************************************)

(*
 * Unary operations.
 *)

(* Identity (polymorphic). *)

declare idOp

(* Naml ints. *)

declare uminusIntOp
declare notIntOp

(* Bit fields. *)

declare rawBitFieldOp{ 'int_precision; 'int_signed; 'int1; 'int2 }

(* Native ints. *)

declare uminusRawIntOp{ 'int_precision; 'int_signed }
declare notRawIntOp{ 'int_precision; 'int_signed }

(* Floats. *)

declare uminusFloatOp{ 'float_precision }
declare absFloatOp{ 'float_precision }
declare sinOp{ 'float_precision }
declare cosOp{ 'float_precision }
declare sqrtOp{ 'float_precision }

(* Coerce to int. *)

declare intOfFloatOp{ 'float_precision }

(* Coerce to float. *)

declare floatOfIntOp{ 'float_precision }
declare floatOfFloatOp{ 'float_precision1; 'float_precision2 }
declare floatOfRawIntOp{ 'float_precision; 'int_precision; 'int_signed }

(* Coerce to rawint. *)

declare rawIntOfIntOp{ 'int_precision; 'int_signed }
declare rawIntOfEnumOp{ 'int_precision; 'int_signed; 'int }
declare rawIntOfFloatOp{ 'int_precision; 'int_signed; 'float_precision }
declare rawIntOfRawIntOp{ 'dest_int_precision; 'dest_int_signed;
                          'src_int_precision;  'src_int_signed }

(* Integer/pointer coercions. *)

declare rawIntOfPointerOp{ 'int_precision; 'int_signed }
declare pointerOfRawIntOp{ 'int_precision; 'int_signed }

(*
 * Binary operations.
 *)

(* Enums. *)

declare andEnumOp{ 'int }
declare orEnumOp{ 'int }
declare xorEnumOp{ 'int }

(* Naml ints. *)

declare plusIntOp
declare minusIntOp
declare mulIntOp
declare divIntOp
declare remIntOp
declare lslIntOp
declare lsrIntOp
declare asrIntOp
declare andIntOp
declare orIntOp
declare xorIntOp
declare maxIntOp
declare minIntOp

declare eqIntOp
declare neqIntOp
declare ltIntOp
declare leIntOp
declare gtIntOp
declare geIntOp
declare cmpIntOp

(* Native ints. *)

declare plusRawIntOp{ 'int_precision; 'int_signed }
declare minusRawIntOp{ 'int_precision; 'int_signed }
declare mulRawIntOp{ 'int_precision; 'int_signed }
declare divRawIntOp{ 'int_precision; 'int_signed }
declare remRawIntOp{ 'int_precision; 'int_signed }
declare slRawIntOp{ 'int_precision; 'int_signed }
declare srRawIntOp{ 'int_precision; 'int_signed }
declare andRawIntOp{ 'int_precision; 'int_signed }
declare orRawIntOp{ 'int_precision; 'int_signed }
declare xorRawIntOp{ 'int_precision; 'int_signed }
declare maxRawIntOp{ 'int_precision; 'int_signed }
declare minRawIntOp{ 'int_precision; 'int_signed }

declare rawSetBitFieldOp{ 'int_precision; 'int_signed; 'int1; 'int2 }

declare eqRawIntOp{ 'int_precision; 'int_signed }
declare neqRawIntOp{ 'int_precision; 'int_signed }
declare ltRawIntOp{ 'int_precision; 'int_signed }
declare leRawIntOp{ 'int_precision; 'int_signed }
declare gtRawIntOp{ 'int_precision; 'int_signed }
declare geRawIntOp{ 'int_precision; 'int_signed }
declare cmpRawIntOp{ 'int_precision; 'int_signed }

(* Floats. *)

declare plusFloatOp{ 'float_precision }
declare minusFloatOp{ 'float_precision }
declare mulFloatOp{ 'float_precision }
declare divFloatOp{ 'float_precision }
declare remFloatOp{ 'float_precision }
declare maxFloatOp{ 'float_precision }
declare minFloatOp{ 'float_precision }

declare eqFloatOp{ 'float_precision }
declare neqFloatOp{ 'float_precision }
declare ltFloatOp{ 'float_precision }
declare leFloatOp{ 'float_precision }
declare gtFloatOp{ 'float_precision }
declare geFloatOp{ 'float_precision }
declare cmpFloatOp{ 'float_precision }

declare atan2Op{ 'float_precision }

(* Pointer equality. *)

declare eqEqOp
declare neqEqOp

(* Pointer arithmetic. *)

declare plusPointerOp{ 'int_precision; 'int_signed }

(*
 * Subscript operators.
 *)

(* Blocks. *)

declare blockSub
declare rawDataSub
declare tupleSub
declare rawTupleSub

(* Values. *)

declare polySub
declare rawIntSub{ 'int_precision; 'int_signed }
declare rawFloatSub{ 'float_precision }
declare pointerSub
declare functionSub

(* Indexing. *)

declare byteIndex
declare wordIndex

(* Subscripting. *)

declare intIndex
declare rawIntIndex{ 'int_precision; 'int_signed }

(* Subscripting op. *)

declare subop{ 'sub_block; 'sub_value; 'sub_index; 'sub_script }

(*
 * Normal values.
 *)

declare atomNil{ 'ty }
declare atomInt{ 'int }
declare atomEnum{ 'int1; 'int2 }
declare atomRawInt{ 'int_precision; 'int_signed; 'num }
declare atomFloat{ 'float_precision; 'num }
declare atomConst{ 'ty; 'ty_var; 'int }
declare atomVar{ 'var }

(*
 * Allocation operators.
 *)

declare allocTuple{ 'tuple_class; 'ty; 'atom_list }
declare allocUnion{ 'ty; 'ty_var; 'int; 'atom_list }
declare allocArray{ 'ty; 'atom_list }
declare allocVArray{ 'ty; 'sub_index; 'atom1; 'atom2 }
declare allocMalloc{ 'ty; 'atom }

(*
 * Tail calls / operations.
 *)

declare tailSysMigrate{ 'int; 'atom1; 'atom2; 'var; 'atom_list }
declare tailAtomic{ 'var; 'atom; 'atom_list }
declare tailAtomicRollback{ 'atom }
declare tailAtomicCommit{ 'var; 'atom_list }

(*
 * Predicates and assertions.
 *)

(* No-ops. *)

declare isMutable

(* Unary operations. *)

declare reserve
declare boundsCheckLower
declare boundsCheckUpper
declare polyCheck
declare pointerCheck
declare functionCheck

(* Binary operations. *)

declare boundsCheck

(* Predicates. *)

declare predNop{ 'var; 'pred_nop }
declare predUnop{ 'var; 'pred_unop; 'atom }
declare predBinop{ 'var; 'pred_binop; 'atom1; 'atom2 }

(*
 * Debugging info.
 *)

declare debugLine{ 'string; 'int }
declare debugVarItem{ 'var1; 'ty; 'var2 }
declare debugVars{ 'debugVarItem_list }
declare debugString{ 'string }
declare debugContext{ 'debug_line; 'debug_vars }

(*
 * Expressions.
 *)

(* Primitive operations. *)

declare letUnop{ 'ty; 'unop; 'atom; var. 'exp['var] }
declare letBinop{ 'ty; 'binop; 'atom1; 'atom2; var. 'exp['var] }

(* Function application. *)

declare letExt{ 'ty1; 'string; 'ty2; 'atom_list; var. 'exp['var] }
declare tailCall{ 'var; 'atom_list }
declare specialCall{ 'tailop }

(* Control. *)

declare matchCase{ 'set; 'exp }
declare matchExp{ 'atom; 'matchCase_list }
declare typeCase{ 'atom1; 'atom2; 'var1; 'var2; 'exp1; 'exp2 }

(* Allocation. *)

declare letAlloc{ 'alloc_op; var. 'exp['var] }

(* Subscripting. *)

declare letSubscript{ 'subop; 'ty; 'var2; 'atom; var1. 'exp['var1] }
declare setSubscript{ 'subop; 'label; 'var; 'atom1; 'ty; 'atom2; 'exp }
declare setGlobal{ 'sub_value; 'label; 'var; 'ty; 'atom; 'exp }
declare memcpy{ 'subop; 'label; 'var1; 'atom1; 'var2; 'atom2; 'atom3; 'exp }

(* Assertions. *)

declare call{ 'var; 'atom_option_list; 'exp }
declare assertExp{ 'label; 'pred; 'exp }

(* Debugging. *)

declare debug{ 'debug_info; 'exp }

(*************************************************************************
 * Term operations.
 *************************************************************************)

(*
 * Unary operations.
 *)

(* Identity (polymorphic). *)

val idOp_term : term
val is_idOp_term : term -> bool

(* Naml ints. *)

val uminusIntOp_term : term
val is_uminusIntOp_term : term -> bool

val notIntOp_term : term
val is_notIntOp_term : term -> bool

(* Bit fields. *)

val rawBitFieldOp_term : term
val is_rawBitFieldOp_term : term -> bool
val mk_rawBitFieldOp_term : term -> term -> term -> term -> term
val dest_rawBitFieldOp_term : term -> term * term * term * term

(* Native ints. *)

val uminusRawIntOp_term : term
val is_uminusRawIntOp_term : term -> bool
val mk_uminusRawIntOp_term : term -> term -> term
val dest_uminusRawIntOp_term : term -> term * term

val notRawIntOp_term : term
val is_notRawIntOp_term : term -> bool
val mk_notRawIntOp_term : term -> term -> term
val dest_notRawIntOp_term : term -> term * term

(* Floats. *)

val uminusFloatOp_term : term
val is_uminusFloatOp_term : term -> bool
val mk_uminusFloatOp_term : term -> term
val dest_uminusFloatOp_term : term -> term

val absFloatOp_term : term
val is_absFloatOp_term : term -> bool
val mk_absFloatOp_term : term -> term
val dest_absFloatOp_term : term -> term

val sinOp_term : term
val is_sinOp_term : term -> bool
val mk_sinOp_term : term -> term
val dest_sinOp_term : term -> term

val cosOp_term : term
val is_cosOp_term : term -> bool
val mk_cosOp_term : term -> term
val dest_cosOp_term : term -> term

val sqrtOp_term : term
val is_sqrtOp_term : term -> bool
val mk_sqrtOp_term : term -> term
val dest_sqrtOp_term : term -> term

(* Coerce to int. *)

val intOfFloatOp_term : term
val is_intOfFloatOp_term : term -> bool
val mk_intOfFloatOp_term : term -> term
val dest_intOfFloatOp_term : term -> term

(* Coerce to float. *)

val floatOfIntOp_term : term
val is_floatOfIntOp_term : term -> bool
val mk_floatOfIntOp_term : term -> term
val dest_floatOfIntOp_term : term -> term

val floatOfFloatOp_term : term
val is_floatOfFloatOp_term : term -> bool
val mk_floatOfFloatOp_term : term -> term -> term
val dest_floatOfFloatOp_term : term -> term * term

val floatOfRawIntOp_term : term
val is_floatOfRawIntOp_term : term -> bool
val mk_floatOfRawIntOp_term : term -> term -> term -> term
val dest_floatOfRawIntOp_term : term -> term * term * term

(* Coerce to rawint. *)

val rawIntOfIntOp_term : term
val is_rawIntOfIntOp_term : term -> bool
val mk_rawIntOfIntOp_term : term -> term -> term
val dest_rawIntOfIntOp_term : term -> term * term

val rawIntOfEnumOp_term : term
val is_rawIntOfEnumOp_term : term -> bool
val mk_rawIntOfEnumOp_term : term -> term -> term -> term
val dest_rawIntOfEnumOp_term : term -> term * term * term

val rawIntOfFloatOp_term : term
val is_rawIntOfFloatOp_term : term -> bool
val mk_rawIntOfFloatOp_term : term -> term -> term -> term
val dest_rawIntOfFloatOp_term : term -> term * term * term

val rawIntOfRawIntOp_term : term
val is_rawIntOfRawIntOp_term : term -> bool
val mk_rawIntOfRawIntOp_term : term -> term -> term -> term -> term
val dest_rawIntOfRawIntOp_term : term -> term * term * term * term

(* Integer/pointer coercions. *)

val rawIntOfPointerOp_term : term
val is_rawIntOfPointerOp_term : term -> bool
val mk_rawIntOfPointerOp_term : term -> term -> term
val dest_rawIntOfPointerOp_term : term -> term * term

val pointerOfRawIntOp_term : term
val is_pointerOfRawIntOp_term : term -> bool
val mk_pointerOfRawIntOp_term : term -> term -> term
val dest_pointerOfRawIntOp_term : term -> term * term

(*
 * Binary operations.
 *)

(* Enums. *)

val andEnumOp_term : term
val is_andEnumOp_term : term -> bool
val mk_andEnumOp_term : term -> term
val dest_andEnumOp_term : term -> term

val orEnumOp_term : term
val is_orEnumOp_term : term -> bool
val mk_orEnumOp_term : term -> term
val dest_orEnumOp_term : term -> term

val xorEnumOp_term : term
val is_xorEnumOp_term : term -> bool
val mk_xorEnumOp_term : term -> term
val dest_xorEnumOp_term : term -> term

(* Naml ints. *)

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

(* Native ints. *)

val plusRawIntOp_term : term
val is_plusRawIntOp_term : term -> bool
val mk_plusRawIntOp_term : term -> term -> term
val dest_plusRawIntOp_term : term -> term * term

val minusRawIntOp_term : term
val is_minusRawIntOp_term : term -> bool
val mk_minusRawIntOp_term : term -> term -> term
val dest_minusRawIntOp_term : term -> term * term

val mulRawIntOp_term : term
val is_mulRawIntOp_term : term -> bool
val mk_mulRawIntOp_term : term -> term -> term
val dest_mulRawIntOp_term : term -> term * term

val divRawIntOp_term : term
val is_divRawIntOp_term : term -> bool
val mk_divRawIntOp_term : term -> term -> term
val dest_divRawIntOp_term : term -> term * term

val remRawIntOp_term : term
val is_remRawIntOp_term : term -> bool
val mk_remRawIntOp_term : term -> term -> term
val dest_remRawIntOp_term : term -> term * term

val slRawIntOp_term : term
val is_slRawIntOp_term : term -> bool
val mk_slRawIntOp_term : term -> term -> term
val dest_slRawIntOp_term : term -> term * term

val srRawIntOp_term : term
val is_srRawIntOp_term : term -> bool
val mk_srRawIntOp_term : term -> term -> term
val dest_srRawIntOp_term : term -> term * term

val andRawIntOp_term : term
val is_andRawIntOp_term : term -> bool
val mk_andRawIntOp_term : term -> term -> term
val dest_andRawIntOp_term : term -> term * term

val orRawIntOp_term : term
val is_orRawIntOp_term : term -> bool
val mk_orRawIntOp_term : term -> term -> term
val dest_orRawIntOp_term : term -> term * term

val xorRawIntOp_term : term
val is_xorRawIntOp_term : term -> bool
val mk_xorRawIntOp_term : term -> term -> term
val dest_xorRawIntOp_term : term -> term * term

val maxRawIntOp_term : term
val is_maxRawIntOp_term : term -> bool
val mk_maxRawIntOp_term : term -> term -> term
val dest_maxRawIntOp_term : term -> term * term

val minRawIntOp_term : term
val is_minRawIntOp_term : term -> bool
val mk_minRawIntOp_term : term -> term -> term
val dest_minRawIntOp_term : term -> term * term

val rawSetBitFieldOp_term : term
val is_rawSetBitFieldOp_term : term -> bool
val mk_rawSetBitFieldOp_term : term -> term -> term -> term -> term
val dest_rawSetBitFieldOp_term : term -> term * term * term * term

val eqRawIntOp_term : term
val is_eqRawIntOp_term : term -> bool
val mk_eqRawIntOp_term : term -> term -> term
val dest_eqRawIntOp_term : term -> term * term

val eqRawIntOp_term : term
val is_eqRawIntOp_term : term -> bool
val mk_eqRawIntOp_term : term -> term -> term
val dest_eqRawIntOp_term : term -> term * term

val neqRawIntOp_term : term
val is_neqRawIntOp_term : term -> bool
val mk_neqRawIntOp_term : term -> term -> term
val dest_neqRawIntOp_term : term -> term * term

val ltRawIntOp_term : term
val is_ltRawIntOp_term : term -> bool
val mk_ltRawIntOp_term : term -> term -> term
val dest_ltRawIntOp_term : term -> term * term

val leRawIntOp_term : term
val is_leRawIntOp_term : term -> bool
val mk_leRawIntOp_term : term -> term -> term
val dest_leRawIntOp_term : term -> term * term

val gtRawIntOp_term : term
val is_gtRawIntOp_term : term -> bool
val mk_gtRawIntOp_term : term -> term -> term
val dest_gtRawIntOp_term : term -> term * term

val geRawIntOp_term : term
val is_geRawIntOp_term : term -> bool
val mk_geRawIntOp_term : term -> term -> term
val dest_geRawIntOp_term : term -> term * term

val cmpRawIntOp_term : term
val is_cmpRawIntOp_term : term -> bool
val mk_cmpRawIntOp_term : term -> term -> term
val dest_cmpRawIntOp_term : term -> term * term

(* Floats. *)

val plusFloatOp_term : term
val is_plusFloatOp_term : term -> bool
val mk_plusFloatOp_term : term -> term
val dest_plusFloatOp_term : term -> term

val minusFloatOp_term : term
val is_minusFloatOp_term : term -> bool
val mk_minusFloatOp_term : term -> term
val dest_minusFloatOp_term : term -> term

val mulFloatOp_term : term
val is_mulFloatOp_term : term -> bool
val mk_mulFloatOp_term : term -> term
val dest_mulFloatOp_term : term -> term

val divFloatOp_term : term
val is_divFloatOp_term : term -> bool
val mk_divFloatOp_term : term -> term
val dest_divFloatOp_term : term -> term

val remFloatOp_term : term
val is_remFloatOp_term : term -> bool
val mk_remFloatOp_term : term -> term
val dest_remFloatOp_term : term -> term

val maxFloatOp_term : term
val is_maxFloatOp_term : term -> bool
val mk_maxFloatOp_term : term -> term
val dest_maxFloatOp_term : term -> term

val minFloatOp_term : term
val is_minFloatOp_term : term -> bool
val mk_minFloatOp_term : term -> term
val dest_minFloatOp_term : term -> term

val eqFloatOp_term : term
val is_eqFloatOp_term : term -> bool
val mk_eqFloatOp_term : term -> term
val dest_eqFloatOp_term : term -> term

val neqFloatOp_term : term
val is_neqFloatOp_term : term -> bool
val mk_neqFloatOp_term : term -> term
val dest_neqFloatOp_term : term -> term

val ltFloatOp_term : term
val is_ltFloatOp_term : term -> bool
val mk_ltFloatOp_term : term -> term
val dest_ltFloatOp_term : term -> term

val leFloatOp_term : term
val is_leFloatOp_term : term -> bool
val mk_leFloatOp_term : term -> term
val dest_leFloatOp_term : term -> term

val gtFloatOp_term : term
val is_gtFloatOp_term : term -> bool
val mk_gtFloatOp_term : term -> term
val dest_gtFloatOp_term : term -> term

val geFloatOp_term : term
val is_geFloatOp_term : term -> bool
val mk_geFloatOp_term : term -> term
val dest_geFloatOp_term : term -> term

val cmpFloatOp_term : term
val is_cmpFloatOp_term : term -> bool
val mk_cmpFloatOp_term : term -> term
val dest_cmpFloatOp_term : term -> term

val atan2Op_term : term
val is_atan2Op_term : term -> bool
val mk_atan2Op_term : term -> term
val dest_atan2Op_term : term -> term

(* Pointer equality. *)

val eqEqOp_term : term
val is_eqEqOp_term : term -> bool

val neqEqOp_term : term
val is_neqEqOp_term : term -> bool

(* Pointer arithmetic. *)

val plusPointerOp_term : term
val is_plusPointerOp_term : term -> bool
val mk_plusPointerOp_term : term -> term -> term
val dest_plusPointerOp_term : term -> term * term

(*
 * Subscript operators.
 *)

(* Blocks. *)

val blockSub_term : term
val is_blockSub_term : term -> bool

val rawDataSub_term : term
val is_rawDataSub_term : term -> bool

val tupleSub_term : term
val is_tupleSub_term : term -> bool

val rawTupleSub_term : term
val is_rawTupleSub_term : term -> bool

(* Values. *)

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

val pointerSub_term : term
val is_pointerSub_term : term -> bool

val functionSub_term : term
val is_functionSub_term : term -> bool

(* Indexing. *)

val byteIndex_term : term
val is_byteIndex_term : term -> bool

val wordIndex_term : term
val is_wordIndex_term : term -> bool

(* Subscripting. *)

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
 * Normal values.
 *)

val atomNil_term : term
val is_atomNil_term : term -> bool
val mk_atomNil_term : term -> term
val dest_atomNil_term : term -> term

val atomInt_term : term
val is_atomInt_term : term -> bool
val mk_atomInt_term : term -> term
val dest_atomInt_term : term -> term

val atomEnum_term : term
val is_atomEnum_term : term -> bool
val mk_atomEnum_term : term -> term -> term
val dest_atomEnum_term : term -> term * term

val atomRawInt_term : term
val is_atomRawInt_term : term -> bool
val mk_atomRawInt_term : term -> term -> term -> term
val dest_atomRawInt_term : term -> term * term * term

val atomFloat_term : term
val is_atomFloat_term : term -> bool
val mk_atomFloat_term : term -> term -> term
val dest_atomFloat_term : term -> term * term

val atomConst_term : term
val is_atomConst_term : term -> bool
val mk_atomConst_term : term -> term -> term -> term
val dest_atomConst_term : term -> term * term * term

val atomVar_term : term
val is_atomVar_term : term -> bool
val mk_atomVar_term : term -> term
val dest_atomVar_term : term -> term

(*
 * Allocation operators.
 *)

val allocTuple_term : term
val is_allocTuple_term : term -> bool
val mk_allocTuple_term : term -> term -> term -> term
val dest_allocTuple_term : term -> term * term * term

val allocUnion_term : term
val is_allocUnion_term : term -> bool
val mk_allocUnion_term : term -> term -> term -> term -> term
val dest_allocUnion_term : term -> term * term * term * term

val allocArray_term : term
val is_allocArray_term : term -> bool
val mk_allocArray_term : term -> term -> term
val dest_allocArray_term : term -> term * term

val allocVArray_term : term
val is_allocVArray_term : term -> bool
val mk_allocVArray_term : term -> term -> term -> term -> term
val dest_allocVArray_term : term -> term * term * term * term

val allocMalloc_term : term
val is_allocMalloc_term : term -> bool
val mk_allocMalloc_term : term -> term -> term
val dest_allocMalloc_term : term -> term * term

(*
 * Tail calls / operations.
 *)

val tailSysMigrate_term : term
val is_tailSysMigrate_term : term -> bool
val mk_tailSysMigrate_term : term -> term -> term -> term -> term -> term
val dest_tailSysMigrate_term : term -> term * term * term * term * term

val tailAtomic_term : term
val is_tailAtomic_term : term -> bool
val mk_tailAtomic_term : term -> term -> term -> term
val dest_tailAtomic_term : term -> term * term * term

val tailAtomicRollback_term : term
val is_tailAtomicRollback_term : term -> bool
val mk_tailAtomicRollback_term : term -> term
val dest_tailAtomicRollback_term : term -> term

val tailAtomicCommit_term : term
val is_tailAtomicCommit_term : term -> bool
val mk_tailAtomicCommit_term : term -> term -> term
val dest_tailAtomicCommit_term : term -> term * term

(*
 * Predicates and assertions.
 *)

(* No-ops. *)

val isMutable_term : term
val is_isMutable_term : term -> bool

(* Unary operations. *)

val reserve_term : term
val is_reserve_term : term -> bool

val boundsCheckLower_term : term
val is_boundsCheckLower_term : term -> bool

val boundsCheckUpper_term : term
val is_boundsCheckUpper_term : term -> bool

val polyCheck_term : term
val is_polyCheck_term : term -> bool

val pointerCheck_term : term
val is_pointerCheck_term : term -> bool

val functionCheck_term : term
val is_functionCheck_term : term -> bool

(* Binary operations. *)

val boundsCheck_term : term
val is_boundsCheck_term : term -> bool

(* Predicates. *)

val predNop_term : term
val is_predNop_term : term -> bool
val mk_predNop_term : term -> term -> term
val dest_predNop_term : term -> term * term

val predUnop_term : term
val is_predUnop_term : term -> bool
val mk_predUnop_term : term -> term -> term -> term
val dest_predUnop_term : term -> term * term * term

val predBinop_term : term
val is_predBinop_term : term -> bool
val mk_predBinop_term : term -> term -> term -> term -> term
val dest_predBinop_term : term -> term * term * term * term

(*
 * Debugging info.
 *)

val debugLine_term : term
val is_debugLine_term : term -> bool
val mk_debugLine_term : term -> term -> term
val dest_debugLine_term : term -> term * term

val debugVarItem_term : term
val is_debugVarItem_term : term -> bool
val mk_debugVarItem_term : term -> term -> term -> term
val dest_debugVarItem_term : term -> term * term * term

val debugVars_term : term
val is_debugVars_term : term -> bool
val mk_debugVars_term : term -> term
val dest_debugVars_term : term -> term

val debugString_term : term
val is_debugString_term : term -> bool
val mk_debugString_term : term -> term
val dest_debugString_term : term -> term

val debugContext_term : term
val is_debugContext_term : term -> bool
val mk_debugContext_term : term -> term -> term
val dest_debugContext_term : term -> term * term

(*
 * Expressions.
 *)

(* Primitive operations. *)

val letUnop_term : term
val is_letUnop_term : term -> bool
val mk_letUnop_term : term -> term -> term -> string -> term -> term
val dest_letUnop_term : term -> term * term * term * string * term

val letBinop_term : term
val is_letBinop_term : term -> bool
val mk_letBinop_term : term -> term -> term -> term -> string -> term -> term
val dest_letBinop_term : term -> term * term * term * term * string * term

(* Function application. *)

val letExt_term : term
val is_letExt_term : term -> bool
val mk_letExt_term : term -> term -> term -> term -> string -> term -> term
val dest_letExt_term : term -> term * term * term * term * string * term

val tailCall_term : term
val is_tailCall_term : term -> bool
val mk_tailCall_term : term -> term -> term
val dest_tailCall_term : term -> term * term

val specialCall_term : term
val is_specialCall_term : term -> bool
val mk_specialCall_term : term -> term
val dest_specialCall_term : term -> term

(* Control. *)

val matchCase_term : term
val is_matchCase_term : term -> bool
val mk_matchCase_term : term -> term -> term
val dest_matchCase_term : term -> term * term

val matchExp_term : term
val is_matchExp_term : term -> bool
val mk_matchExp_term : term -> term -> term
val dest_matchExp_term : term -> term * term

val typeCase_term : term
val is_typeCase_term : term -> bool
val mk_typeCase_term :
   term -> term -> term -> term -> term -> term -> term
val dest_typeCase_term :
   term-> term * term * term * term * term * term

(* Allocation. *)

val letAlloc_term : term
val is_letAlloc_term : term -> bool
val mk_letAlloc_term : string -> term -> term -> term
val dest_letAlloc_term : term -> string * term * term

(* Subscripting *)

val letSubscript_term : term
val is_letSubscript_term : term -> bool
val mk_letSubscript_term :
   term -> term -> term -> term -> string -> term -> term
val dest_letSubscript_term :
   term -> term * term * term * term * string * term

val setSubscript_term : term
val is_setSubscript_term : term -> bool
val mk_setSubscript_term :
   term -> term -> term -> term -> term -> term -> term -> term
val dest_setSubscript_term :
   term -> term * term * term * term * term * term * term

val setGlobal_term : term
val is_setGlobal_term : term -> bool
val mk_setGlobal_term :
   term -> term -> term -> term -> term -> term -> term
val dest_setGlobal_term :
   term -> term * term * term * term * term * term

val memcpy_term : term
val is_memcpy_term : term -> bool
val mk_memcpy_term :
   term -> term -> term -> term -> term -> term -> term -> term -> term
val dest_memcpy_term :
   term -> term * term * term * term * term * term * term * term

(* Assertions. *)

val call_term : term
val is_call_term : term -> bool
val mk_call_term : term -> term -> term -> term
val dest_call_term : term -> term * term * term

val assertExp_term : term
val is_assertExp_term : term -> bool
val mk_assertExp_term : term -> term -> term -> term
val dest_assertExp_term : term -> term * term * term

(* Debugging. *)

val debug_term : term
val is_debug_term : term -> bool
val mk_debug_term : term -> term -> term
val dest_debug_term : term -> term * term
