(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define and implement operations for ints in the FIR.
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
include Itt_theory
include Fir_ty
include Fir_exp

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Unary and bitwise negation. *)
declare uminusIntOp
declare notIntOp (* not implemented until modular arithmetic is deal with *)

(* Standard binary arithmetic operators. *)
declare plusIntOp
declare minusIntOp
declare mulIntOp
declare divIntOp
declare remIntOp

(*
 * Binary bitwise operators:
 * and, or, xor
 * logical shifts left/right
 * arithmetic shift right
 *
 * These won't actually be implemented until modular arithmetic
 * is properly dealt with.
 *)
declare lslIntOp
declare lsrIntOp
declare asrIntOp
declare andIntOp
declare orIntOp
declare xorIntOp

(* Max / min. *)
declare maxIntOp
declare minIntOp

(* Boolean comparisons. *)
declare eqIntOp
declare neqIntOp
declare ltIntOp
declare leIntOp
declare gtIntOp
declare geIntOp
declare cmpIntOp

(*************************************************************************
 * Rewrites.
 *************************************************************************)

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
