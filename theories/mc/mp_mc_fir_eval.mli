(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define how to evaluate the FIR.
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

include Mp_mc_fir_base
include Mp_mc_fir_ty
include Mp_mc_fir_exp
include Itt_int_base
include Itt_int_ext
include Itt_rfun

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Modular arithmetic for integers.
 *)

(* Precision of naml integers. *)

declare naml_prec

(* Computes base ^ exp where base and exp are integers, with exp non-neg. *)

declare pow{ 'base; 'exp }

(*
 * Converts num to an appropriate value for an integer of precision bytes,
 * signed or unsigned.
 *)

declare mod_arith{ 'int_precision; 'int_signed; 'num }
declare mod_arith_signed{ 'int_precision; 'num }
declare mod_arith_unsigned{ 'int_precision; 'num }

(*
 * Expressions.
 *)

declare unop_exp{ 'op; 'ty; 'a1 }
declare binop_exp{ 'op; 'ty; 'a1; 'a2 }

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(*
 * Modular arithmetic for integers.
 *)

topval reduce_naml_prec : conv
topval reduce_int8 : conv
topval reduce_int16 : conv
topval reduce_int32 : conv
topval reduce_int64 : conv

topval reduce_pow : conv
topval reduce_pow_2_7 : conv
topval reduce_pow_2_8 : conv
topval reduce_pow_2_15 : conv
topval reduce_pow_2_16 : conv
topval reduce_pow_2_30 : conv
topval reduce_pow_2_31 : conv
topval reduce_pow_2_32 : conv
topval reduce_pow_2_63 : conv
topval reduce_pow_2_64 : conv

topval reduce_mod_arith1 : conv  (* signedInt   -> mod_arith_signed   *)
topval reduce_mod_arith2 : conv  (* unsignedInt -> mod_arith_unsigned *)
topval reduce_mod_arith_signed : conv
topval reduce_mod_arith_unsigned : conv

(*
 * Unary operations.
 *)

(* Identity (polymorphic). *)

topval reduce_idOp : conv

(* Naml ints. *)

topval reduce_uminusIntOp : conv

(*
 * Binary operations.
 *)

(* Naml ints. *)

topval reduce_plusIntOp : conv
topval reduce_minusIntOp : conv
topval reduce_mulIntOp : conv
topval reduce_divIntOp : conv
topval reduce_remIntOp : conv
topval reduce_maxIntOp : conv
topval reduce_minIntOp : conv

(* Native ints. *)

topval reduce_plusRawIntOp : conv
topval reduce_minusRawIntOp : conv
topval reduce_mulRawIntOp : conv
topval reduce_divRawIntOp : conv
topval reduce_remRawIntOp : conv
topval reduce_maxRawIntOp : conv
topval reduce_minRawIntOp : conv

(*
 * Normal values.
 *)

topval reduce_atomVar_atomNil : conv
topval reduce_atomVar_atomInt : conv
topval reduce_atomVar_atomEnum : conv
topval reduce_atomVar_atomRawInt : conv
topval reduce_atomVar_atomFloat : conv
topval reduce_atomVar_atomConst : conv

(*
 * Expressions.
 *)

(* Primitive operations. *)

topval reduce_letUnop : conv
topval reduce_letBinop : conv

(*************************************************************************
 * Automation.
 *************************************************************************)

topval firEvalT : int -> tactic
