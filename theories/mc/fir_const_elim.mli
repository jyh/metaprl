(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Fold constants together in FIR expressions.
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
include Fir_eval

open Tactic_type.Conversionals

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(*
 * Naml integers.
 *)

topval const_elim_plusIntOp : conv
topval const_elim_minusIntOp : conv
topval const_elim_mulIntOp : conv
topval const_elim_divIntOp : conv
topval const_elim_remIntOp : conv
topval const_elim_maxIntOp : conv
topval const_elim_minIntOp : conv
topval const_elim_eqIntOp : conv
topval const_elim_neqIntOp : conv
topval const_elim_ltIntOp : conv
topval const_elim_leIntOp : conv
topval const_elim_gtIntOp : conv
topval const_elim_geIntOp : conv
topval const_elim_cmpIntOp : conv

(*
 * Native integers.
 *)

topval const_elim_plusRawIntOp : conv
topval const_elim_minusRawIntOp : conv
topval const_elim_mulRawIntOp : conv
topval const_elim_divRawIntOp : conv
topval const_elim_remRawIntOp : conv
topval const_elim_maxRawIntOp : conv
topval const_elim_minRawIntOp : conv
topval const_elim_eqRawIntOp : conv
topval const_elim_neqRawIntOp : conv
topval const_elim_ltRawIntOp : conv
topval const_elim_leRawIntOp : conv
topval const_elim_gtRawIntOp : conv
topval const_elim_geRawIntOp : conv
topval const_elim_cmpRawIntOp : conv

(*************************************************************************
 * Automation.
 *************************************************************************)

topval firConstElimT : int -> tactic
