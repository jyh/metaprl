(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define and implement the basic expression forms in the FIR.
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
declare rawBitFieldOp{ 'precision; 'sign; 'num1; 'num2 }

(* Native ints. *)
declare uminusRawIntOp{ 'precision; 'sign }
declare notRawIntOp{ 'precision; 'sign }

(* Floats. *)
declare uminusFloatOp{ 'precision }
declare absFloatOp{ 'precision }
declare sinOp{ 'precision }
declare cosOp{ 'precision }
declare sqrtOp{ 'precision }

(* Coerce to int. *)
declare intOfFloatOp{ 'precision }

(* Coerce to float. *)
declare floatOfIntOp{ 'precision }
declare floatOfFloatOp{ 'prec1; 'prec2 }
declare floatOfRawIntOp{ 'float_prec; 'int_prec; 'int_sign }

(* Coerce to rawint. *)
declare rawIntOfEnumOp{ 'precision; 'sign; 'num }
declare rawIntOfFloatOp{ 'int_prec; 'int_sign; 'float_prec }
declare rawIntOfRawIntOp{ 'dest_prec; 'dest_sign; 'src_prec; 'src_sign }

(* Integer/pointer coercions. *)
declare rawIntOfPointerOp{ 'precision; 'sign }
declare pointerOfRawIntOp{ 'precision; 'sign }

(*
 * Binary operations.
 *)

(* Enums. *)
declare andEnumOp{ 'num }
declare orEnumOp{ 'num }

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
declare plusRawIntOp{ 'precision; 'sign }
declare minusRawIntOp{ 'precision; 'sign }
declare mulRawIntOp{ 'precision; 'sign }
declare divRawIntOp{ 'precision; 'sign }
declare remRawIntOp{ 'precision; 'sign }
declare slRawIntOp{ 'precision; 'sign }
declare srRawIntOp{ 'precision; 'sign }
declare andRawIntOp{ 'precision; 'sign }
declare orRawIntOp{ 'precision; 'sign }
declare xorRawIntOp{ 'precision; 'sign }
declare maxRawIntOp{ 'precision; 'sign }
declare minRawIntOp{ 'precision; 'sign }

declare rawSetBitFieldOp{ 'precision; 'sign; 'num1; 'num2 }

declare eqRawIntOp{ 'precision; 'sign }
declare neqRawIntOp{ 'precision; 'sign }
declare ltRawIntOp{ 'precision; 'sign }
declare leRawIntOp{ 'precision; 'sign }
declare gtRawIntOp{ 'precision; 'sign }
declare geRawIntOp{ 'precision; 'sign }
declare cmpRawIntOp{ 'precision; 'sign }

(* Floats. *)
declare plusFloatOp{ 'precision }
declare minusFloatOp{ 'precision }
declare mulFloatOp{ 'precision }
declare divFloatOp{ 'precision }
declare remFloatOp{ 'precision }
declare maxFloatOp{ 'precision }
declare minFloatOp{ 'precision }

declare eqFloatOp{ 'precision }
declare neqFloatOp{ 'precision }
declare ltFloatOp{ 'precision }
declare leFloatOp{ 'precision }
declare gtFloatOp{ 'precision }
declare geFloatOp{ 'precision }
declare cmpFloatOp{ 'precision }

declare atan2Op{ 'precision }

(* Pointer equality. *)
declare eqEqOp
declare neqEqOp

(*
 * Subscript operators.
 *)
declare blockPolySub
declare blockRawIntSub{ 'precision; 'sign }
declare blockFloatSub{ 'precision }
declare rawRawIntSub{ 'precision; 'sign }
declare rawFloatSub{ 'precision }
declare rawDataSub
declare rawFunctionSub

(*
 * Allocation operators.
 *)
declare allocTuple{ 'ty; 'atom_list }
declare allocArray{ 'ty; 'atom_list }
declare allocUnion{ 'ty; 'ty_var; 'num; 'atom_list }
declare allocMalloc{ 'atom }

(*
 * Normal values.
 *)
declare atomInt{ 'int }
declare atomEnum{ 'bound; 'num }
declare atomRawInt{ 'precision; 'sign; 'num }
declare atomFloat{ 'f }
declare atomConst{ 'ty; 'ty_var; 'num }
declare atomVar{ 'var }

(*
 * Expressions.
 *)

(* Primitive operations. *)
declare letUnop{ 'op; 'ty; 'a1; v. 'exp['v] }
declare letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp['v] }

(* Function application. *)
declare letExt{ 'ty; 'string; 'ty_of_str; 'atom_list; v. 'exp['v] }
declare tailCall{ 'var; 'atom_list }

(*
 * Control.
 * A matchCase consists of an int_set and an expression.
 * A match statement has a 'key (a number/int or block), and a list
 * of matchCases.
 *)
declare matchCase{ 'set; 'exp }
declare "match"{ 'key; 'cases }

(* Allocation. *)
declare letAlloc{ 'alloc_op; v. 'exp['v] }

(*
 * Subscripting.
 * In setSubscript, we bind the updated value to v in 'exp.
 *)
declare letSubscript{ 'subop; 'ty; 'var; 'index; v. 'exp['v] }
declare setSubscript{ 'subop; 'ty; 'var; 'index; 'new_val; v. 'exp['v] }
declare memcpy{ 'subop; 'var1; 'atom1; 'var2; 'atom2; 'len; 'exp }

(*************************************************************************
 * Term operations.
 *************************************************************************)

(*******************
 * Unary operations.
 *******************)

(* Identity (polymorphic). *)

val idOp_term : term
val is_idOp_term : term -> bool

(* Naml ints. *)

val uminusIntOp_term : term
val is_uminusIntOp_term : term -> bool

val notIntOp_term : term
val is_notIntOp_term : term -> bool

(* Bit fields. *)

(* raw bit field op goes ehre *)

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
val mk_rawIntOfRawIntOp_term : term -> term -> term -> term
val dest_rawIntOfRawIntOp_term : term -> term * term * term

(* Integer/pointer coercions. *)

val rawIntOfPointerOp_term : term
val is_rawIntOfPointerOp_term : term -> bool
val mk_rawIntOfPointerOp_term : term -> term -> term
val dest_rawIntOfPointerOp_term : term -> term * term

val pointerOfRawIntOp_term : term
val is_pointerOfRawIntOp_term : term -> bool
val mk_pointerOfRawIntOp_term : term -> term -> term
val dest_pointerOfRawIntOp_term : term -> term * term

(********************
 * Binary operations.
 ********************)

(* Enums. *)

val andEnumOp_term : term
val is_andEnumOp_term : term -> bool
val mk_andEnumOp_term : term -> term
val dest_andEnumOp_term : term -> term

val orEnumOp_term : term
val is_orEnumOp_term : term -> bool
val mk_orEnumOp_term : term -> term
val dest_orEnumOp_term : term -> term

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

(* that bit field op goes here *)

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

(**********************
 * Subscript operators.
 **********************)
