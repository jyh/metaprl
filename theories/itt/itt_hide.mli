(*
 * Hide type.
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
 * Author: Alexei Kopylov
 * kopylov@cs.cornell.edu
 *
 *)

include Itt_equal
include Itt_subtype
include Itt_unit
include Itt_struct

open Refiner.Refiner.Term

open Tactic_type.Tacticals

declare hide{'A}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)


(*
 * H >- Ui ext hide(A)
 * by setFormation a A
 * H >- Ui ext A
 *)
rule hideFormation 'H 'A :
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

rule hideEquality 'H  :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   sequent ['ext] { 'H >- hide{'A2} = hide{'A1} in univ[i:l] }

rule hideType 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{.hide{'A}} }


rule hideMemberFormation 'H :
   sequent [squash] { 'H >- 'A } -->
   sequent ['ext]   { 'H >- hide{'A} }

rule hideMemberEquality 'H :
   sequent [squash] { 'H >- 'A } -->
   sequent ['ext] { 'H >- it IN hide{'A} }

rule unhideEqual 'H 'J 'u :
   sequent ['ext] { 'H; u: 'x = 'y in 'A; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; u: hide{('x = 'y in 'A)}; 'J['u] >- 'C['u] }

rule unhideGoalEqual 'H 'J 'u :
   sequent [squash] { 'H; u: 'P; 'J[it] >- 'x[it] = 'y[it] in 'T[it] } -->
   sequent ['ext] { 'H; u: hide{'P}; 'J['u] >- 'x['u] = 'y['u] in 'T['u] }



(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(* Hiding and unhiding *)
topval squashT : tactic
topval unhideT : int -> tactic

(* Primitives *)

val is_hide_term : term -> bool
val dest_hide : term -> term
val mk_hide_term : term -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
