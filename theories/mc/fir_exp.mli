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
declare atomRawInt{ 'num }
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
