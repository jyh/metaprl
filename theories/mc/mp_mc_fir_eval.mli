(*
 * The Mp_mc_fir_eval module defines the operational semantics
 * of the FIR.
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
 * Email:  emre@its.caltech.edu
 *)

extends Itt_bool
extends Itt_int_base
extends Itt_int_ext
extends Itt_list
extends Mp_mc_fir_base
extends Mp_mc_fir_ty
extends Mp_mc_fir_exp

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Modular arithmetic for integers.
 *)

(* Precision of naml integers. Corresponds to tyInt. *)

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
 * Booleans, as represented in the FIR.
 *)

declare fir_true
declare fir_false

(*
 * Set (and interval) membership.
 *)

declare member{ 'value; 'set }

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

topval reduce_arith_signed_int8 : conv
topval reduce_arith_signed_int16 : conv
topval reduce_arith_signed_int32 : conv
topval reduce_arith_signed_int64 : conv
topval reduce_arith_signed_naml : conv
topval reduce_arith_unsigned_int8 : conv
topval reduce_arith_unsigned_int16 : conv
topval reduce_arith_unsigned_int32 : conv
topval reduce_arith_unsigned_int64 : conv

topval reduce_mod_arith_signed : conv
topval reduce_mod_arith_unsigned : conv

(*
 * Booleans, as represented in the FIR.
 *)

topval reduce_fir_true : conv
topval reduce_fir_false : conv

(*
 * Set (and interval) membership.
 *)

topval reduce_member_interval : conv
topval reduce_member_int_set : conv
topval reduce_member_rawint_set : conv
topval reduce_member_int_set_empty : conv
topval reduce_member_rawint_set_empty : conv

(*
 * Normal values.
 *)

topval reduce_atomVar_atomNil : conv
topval reduce_atomVar_atomInt : conv
topval reduce_atomVar_atomEnum : conv
topval reduce_atomVar_atomRawInt : conv
topval reduce_atomVar_atomFloat : conv
topval reduce_atomVar_atomLabel : conv
topval reduce_atomVar_atomSizeof : conv
topval reduce_atomVar_atomConst : conv

(*
 * Unary operations.
 *)

topval reduce_idOp_atomInt : conv
topval reduce_idOp_atomEnum : conv
topval reduce_idOp_atomRawInt : conv
topval reduce_idOp_atomFloat : conv
topval reduce_idOp_atomVar : conv

(*
 * Binary operations.
 *)

topval reduce_plusIntOp : conv
topval reduce_minusIntOp : conv
topval reduce_mulIntOp : conv
topval reduce_eqIntOp : conv

topval reduce_plusRawIntOp : conv
topval reduce_minusRawIntOp : conv
topval reduce_mulRawIntOp : conv
topval reduce_eqRawIntOp : conv

topval reduce_eqEqOp : conv

topval reduce_matchExp_atomEnum : conv
topval reduce_matchExp_atomInt : conv
topval reduce_matchExp_number : conv

(*************************************************************************
 * Automation.
 *************************************************************************)

topval firExpEvalC : conv
