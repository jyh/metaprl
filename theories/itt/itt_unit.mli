(*
 * Although unit is not strictly necessary,
 * we define it anyway, so we can use it before numbers
 * are defined.
 *
 * Type unit contains one element, it.
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
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

include Tacticals

include Itt_equal

open Refiner.Refiner.Term

open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare unit

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Squiggle equality.
 *)
rule unitSqequal 'H :
   sequent [squash] { 'H >- 'x = 'y in unit } -->
   sequent ['ext] { 'H >- Perv!"rewrite"{'x; 'y} }

(*
 * H >- Ui ext Unit
 * by unitFormation
 *)
rule unitFormation 'H : sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- Unit = Unit in Ui ext Ax
 * by unitEquality
 *)
rule unitEquality 'H : sequent ['ext] { 'H >- unit = unit in univ[@i:l] }

(*
 * Is a type.
 *)
rule unitType 'H : sequent ['ext] { 'H >- "type"{unit} }

(*
 * H >- Ui ext Unit
 * by unitFormation
 *)
rule unit_memberFormation 'H : sequent ['ext] { 'H >- unit }

(*
 * H >- Unit = Unit in Ui ext Ax
 * by unitEquality
 *)
rule unit_memberEquality 'H : sequent ['ext] { 'H >- it = it in unit }

(*
 * H; i:x:Unit; J >- C
 * by unitElimination i
 * H; i:x:Unit; J[it / x] >- C[it / x]
 *)
rule unitElimination 'H 'J :
   sequent['ext] { 'H; x: unit; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: unit; 'J['x] >- 'C['x] }

(*
 * Squash elimination.
 *)
rule unit_squashElimination 'H :
   sequent [squash] { 'H >- unit } -->
   sequent ['ext] { 'H >- unit }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_unitT : int -> tactic
val eqcd_unitT : tactic
val eqcd_itT : tactic
val unit_term : term

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
