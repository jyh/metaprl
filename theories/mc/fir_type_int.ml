(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Type judgements for integer operations.  These mainly help automation.
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
include Fir_exp
include Fir_int
include Fir_type

open Base_dtactic

(*************************************************************************
 * Rules.
 *************************************************************************)

(*
 * We use intentional equalities here.
 * Working out all the applicable rules of arithmetic would be
 *    tedious, and even then, the rule set wouldn't be complete.
 *)

(*
 * Unary and bitwise negation.
 *)

interactive uminusIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in tyInt } -->
   sequent ['ext] { 'H >-
      unop_exp{ uminusIntOp; 'a1 } =
      unop_exp{ uminusIntOp; 'a2 } in tyInt }

(*
 * Standard binary arithmetic operators.
 *)

interactive plusIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in tyInt } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in tyInt } -->
   sequent ['ext] { 'H >-
      binop_exp{ plusIntOp; 'a1; 'a2 } =
      binop_exp{ plusIntOp; 'b1; 'b2 } in tyInt }

interactive minusIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in tyInt } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in tyInt } -->
   sequent ['ext] { 'H >-
      binop_exp{ minusIntOp; 'a1; 'a2 } =
      binop_exp{ minusIntOp; 'b1; 'b2 } in tyInt }

interactive mulIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in tyInt } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in tyInt } -->
   sequent ['ext] { 'H >-
      binop_exp{ mulIntOp; 'a1; 'a2 } =
      binop_exp{ mulIntOp; 'b1; 'b2 } in tyInt }

interactive divIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a IN tyInt } -->
   [wf] sequent [squash] { 'H >- 'b IN tyInt } -->
   [wf] sequent [squash] { 'H >- "nequal"{ 'b; 0 } } -->
   sequent ['ext] { 'H >- binop_exp{ divIntOp; 'a; 'b } IN tyInt }

interactive remIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a IN tyInt } -->
   [wf] sequent [squash] { 'H >- 'b IN tyInt } -->
   [wf] sequent [squash] { 'H >- "nequal"{ 'b; 0 } } -->
   sequent ['ext] { 'H >- binop_exp{ remIntOp; 'a; 'b } IN tyInt }

(*
 * Binary bitwise operators.
 *)

(* Not implemented yet. *)

(*
 * Max / min.
 *)

interactive maxIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in tyInt } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in tyInt } -->
   sequent ['ext] { 'H >-
      binop_exp{ maxIntOp; 'a1; 'a2 } =
      binop_exp{ maxIntOp; 'b1; 'b2 } in tyInt }

interactive minIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in tyInt } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in tyInt } -->
   sequent ['ext] { 'H >-
      binop_exp{ minIntOp; 'a1; 'a2 } =
      binop_exp{ minIntOp; 'b1; 'b2 } in tyInt }

(*
 * Boolen comparisons.
 *)

interactive eqIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in tyInt } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in tyInt } -->
   sequent ['ext] { 'H >-
      binop_exp{ eqIntOp; 'a1; 'a2 } =
      binop_exp{ eqIntOp; 'b1; 'b2 } in tyInt }

interactive neqIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in tyInt } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in tyInt } -->
   sequent ['ext] { 'H >-
      binop_exp{ neqIntOp; 'a1; 'a2 } =
      binop_exp{ neqIntOp; 'b1; 'b2 } in tyInt }

interactive ltIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in tyInt } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in tyInt } -->
   sequent ['ext] { 'H >-
      binop_exp{ ltIntOp; 'a1; 'a2 } =
      binop_exp{ ltIntOp; 'b1; 'b2 } in tyInt }

interactive leIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in tyInt } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in tyInt } -->
   sequent ['ext] { 'H >-
      binop_exp{ leIntOp; 'a1; 'a2 } =
      binop_exp{ leIntOp; 'b1; 'b2 } in tyInt }

interactive gtIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in tyInt } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in tyInt } -->
   sequent ['ext] { 'H >-
      binop_exp{ gtIntOp; 'a1; 'a2 } =
      binop_exp{ gtIntOp; 'b1; 'b2 } in tyInt }

interactive geIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in tyInt } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in tyInt } -->
   sequent ['ext] { 'H >-
      binop_exp{ geIntOp; 'a1; 'a2 } =
      binop_exp{ geIntOp; 'b1; 'b2 } in tyInt }

interactive cmpIntOp_equality {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in tyInt } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in tyInt } -->
   sequent ['ext] { 'H >-
      binop_exp{ cmpIntOp; 'a1; 'a2 } =
      binop_exp{ cmpIntOp; 'b1; 'b2 } in tyInt }
