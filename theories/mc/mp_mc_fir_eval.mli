(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define how to evaluate the FIR in MetaPRL.
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

include Mp_mc_set
include Fir_ty
include Fir_exp
include Itt_list2
include Itt_int_base
include Itt_int_ext

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

declare mod_arith{ 'precision; 'sign; 'num }
declare mod_arith_signed{ 'precision; 'num }
declare mod_arith_unsigned{ 'precision; 'num }

(*
 * Boolean type.
 * true_set and false_set define true and false for use in matches.
 * I also put a test for atomEnum here since they are used to
 *    represent val_true and val_false.
 *)

declare true_set
declare false_set
declare atomEnum_eq{ 'a; 'b }

(*
 * Functions.
 *)

declare lambda{ x. 'f['x] }   (* for functions with >= 1 arguments *)
declare lambda{ 'f }          (* function with no arguments *)
declare apply{ 'f; 'x }
declare fix{ f. 'b['f] }

(*
 * Expressions.
 *)

declare unop_exp{ 'op; 'ty; 'a1 }
declare binop_exp{ 'op; 'ty; 'a1; 'a2 }

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Modular arithmetic for integers. *)

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

topval reduce_mod_arith : conv
topval reduce_mod_arith_signed : conv
topval reduce_mod_arith_unsigned : conv

(* Boolean type. *)

topval reduce_true_set : conv
topval reduce_false_set : conv
topval reduce_val_true : conv
topval reduce_val_false : conv
topval reduce_atomEnum_eq_atom : conv
topval reduce_atomEnum_eq_num : conv

(* Functions. *)

topval reduce_beta : conv
topval reduce_apply_nil : conv
topval reduce_fix : conv

(* Types. *)

topval reduce_tyVar : conv

(* Expressions. *)

topval reduce_idOp : conv
topval reduce_atomInt : conv
topval reduce_atomEnum : conv
topval reduce_atomRawInt : conv
topval reduce_atomVar : conv
topval reduce_letUnop : conv
topval reduce_letBinop : conv
topval reduce_letExt : conv
topval reduce_allocTuple : conv
topval reduce_allocArray : conv
topval reduce_letSubscript : conv
topval reduce_setSubscript : conv

(* Naml integers. *)

topval reduce_uminusIntOp : conv
topval reduce_plusIntOp : conv
topval reduce_minusIntOp : conv
topval reduce_mulIntOp : conv
topval reduce_divIntOp : conv
topval reduce_remIntOp : conv
topval reduce_maxIntOp : conv
topval reduce_minIntOp : conv
topval reduce_eqIntOp : conv
topval reduce_neqIntOp : conv
topval reduce_ltIntOp : conv
topval reduce_leIntOp : conv
topval reduce_gtIntOp : conv
topval reduce_geIntOp : conv
topval reduce_cmpIntOp : conv

(* Native integers. *)

topval reduce_plusRawIntOp : conv
topval reduce_minusRawIntOp : conv
topval reduce_mulRawIntOp : conv
topval reduce_divRawIntOp : conv
topval reduce_remRawIntOp : conv
topval reduce_maxRawIntOp : conv
topval reduce_minRawIntOp : conv
topval reduce_eqRawIntOp : conv
topval reduce_neqRawIntOp : conv
topval reduce_ltRawIntOp : conv
topval reduce_leRawIntOp : conv
topval reduce_gtRawIntOp : conv
topval reduce_geRawIntOp : conv
topval reduce_cmpRawIntOp : conv

(*************************************************************************
 * Automation.
 *************************************************************************)

topval firEvalT : int -> tactic
