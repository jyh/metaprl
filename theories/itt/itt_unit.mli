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

extends Itt_squiggle

open Refiner.Refiner.Term

open Tactic_type.Tacticals

declare unit

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Squiggle equality.
 *)
rule unitSqequal :
   sequent [squash] { <H> >- 'x = 'y in unit } -->
   sequent ['ext] { <H> >- 'x ~ 'y }

(*
 * H >- Ui ext Unit
 * by unitFormation
 *)
rule unitFormation : sequent ['ext] { <H> >- univ[i:l] }

(*
 * H >- Unit = Unit in Ui ext Ax
 * by unitEquality
 *)
rule unitEquality : sequent ['ext] { <H> >- unit in univ[i:l] }

(*
 * Is a type.
 *)
rule unitType : sequent ['ext] { <H> >- "type"{unit} }

(*
 * H >- Ui ext Unit
 * by unitFormation
 *)
rule unit_memberFormation : sequent ['ext] { <H> >- unit }

(*
 * H >- Unit = Unit in Ui ext Ax
 * by unitEquality
 *)
rule unit_memberEquality : sequent ['ext] { <H> >- it in unit }

(*
 * H; i:x:Unit; J >- C
 * by unitElimination i
 * H; i:x:Unit; J[it / x] >- C[it / x]
 *)
rule unitElimination 'H :
   sequent['ext] { <H>; .unit; <J[it]> >- 'C[it] } -->
   sequent ['ext] { <H>; x: unit; <J['x]> >- 'C['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val unit_term : term
val is_unit_term : term -> bool

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
