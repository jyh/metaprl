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

include Fir_int_set
include Fir_ty
include Fir_exp

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Boolean type.
 * true_set and false_set define true and false for use in matches.
 * val_true and val_false should be used for returning true and false
 *    in FIR evaluation.
 *)
declare true_set
declare false_set
declare val_true
declare val_false

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

declare unop_exp{ 'op; 'a1 }
declare binop_exp{ 'op; 'a1; 'a2 }

(*
 * Misc.
 * Not FIR terms, but used to make output from mc manageable.
 *)

declare unknownFun

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Boolean type. *)

topval reduce_true_set : conv
topval reduce_false_set : conv
topval reduce_val_true : conv
topval reduce_val_false : conv

(* Functions. *)

topval reduce_beta : conv
topval reduce_apply_nil : conv
topval reduce_fix : conv

(* Types. *)

topval reduce_tyVar : conv

(* Expressions. *)

topval reduce_idOp : conv
topval reduce_eqEqOp : conv
topval reduce_neqEqOp : conv
topval reduce_atomInt : conv
topval reduce_atomEnum : conv
topval reduce_atomRawInt : conv
topval reduce_atomVar : conv
topval reduce_letUnop : conv
topval reduce_letBinop : conv
topval reduce_letExt : conv
topval reduce_match_int : conv
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

(*************************************************************************
 * Automation.
 *************************************************************************)

topval firEvalT : int -> tactic
