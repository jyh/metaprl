(*
 * Set type.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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
 *
 *)

include Itt_equal
include Itt_subtype
include Itt_unit
include Itt_struct

open Refiner.Refiner.Term

open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare set{'A; x. 'B['x]}
declare hide{'A}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext { a:A | B }
 * by setFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
axiom setFormation 'H 'a 'A :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   sequent ['ext] { 'H; a: 'A >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- { a1:A1 | B1[a1] } = { a2:A2 | B2[a2] } in Ui
 * by setEquality x
 *
 * H >- A1 = A2 in Ui
 * H, x: A1 >- B1[x] = B2[x] in Ui
 *)
axiom setEquality 'H 'x :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[@i:l] } -->
   sequent ['ext] { 'H >- { a1:'A1 | 'B1['a1] } = { a2:'A2 | 'B2['a2] } in univ[@i:l] }

(*
 * H >- { a:A | B[a] } ext a
 * by setMemberFormation Ui a z
 *
 * H >- a = a in A
 * H >- B[a]
 * H, z: A >- B[z] = B[z] in Ui
 *)
axiom setMemberFormation 'H 'a 'z :
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext]   { 'H >- 'B['a] } -->
   sequent [squash] { 'H; z: 'A >- "type"{'B['z]} } -->
   sequent ['ext]   { 'H >- { x:'A | 'B['x] } }

(*
 * H >- a1 = a2 in { a:A | B }
 * by setMemberEquality Ui x
 *
 * H >- a1 = a2 in A
 * H >- B[a1]
 * H, x: A >- B[x] = B[x] in Ui
 *)
axiom setMemberEquality 'H 'x :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'B['a1] } -->
   sequent [squash] { 'H; x: 'A >- "type"{'B['x]} } -->
   sequent ['ext]   { 'H >- 'a1 = 'a2 in { a:'A | 'B['a] } }

(*
 * H, u: { x:A | B }, J[u] >- T[u] ext t[y]
 * by setElimination y v
 *
 * H, u: { x:A | B }, y: A; v: hide{B[y]}; J[y] >- T[y]
 *)
axiom setElimination 'H 'J 'u 'y 'v :
   sequent [squash] { 'H; u: { x:'A | 'B['x] }; y: 'A; v: 'B['y]; 'J['y] >- 'T['y] } -->
   sequent [squash] { 'H; u: { x:'A | 'B['x] }; 'J['u] >- 'T['u] }

(*
 * H, u: { x:A | B }, J[u] >> T[u] ext t[y]
 * by setElimination2 y v z
 * H, u: { x:A | B }, y: A; v: hide(B[y]); J[y] >> T[y]
 *)
axiom setElimination2 'H 'J 'u 'y 'v :
   sequent [it; 'prop] { 'H; u: { x:'A | 'B['x] }; y: 'A; v: hide{'B['y]}; 'J['y] >- 'T['y] } -->
   sequent [it; 'prop] { 'H; u: { x:'A | 'B['x] }; 'J['u] >- 'T['u] }

(*
 * Unhiding.
 *)
axiom hideElimination 'H 'J :
   sequent [squash] { 'H; u: 'P; 'J[it] >- 'T[it] } -->
   sequent [squash] { 'H; u: hide{'P}; 'J['u] >- 'T['u] }

(*
 * Subtyping.
 *)
axiom set_subtype 'H :
   sequent [squash] { 'H >- "type"{ { a: 'A | 'B['a] } } } -->
   sequent ['ext] { 'H >- subtype{ { a: 'A | 'B['a] }; 'A } }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_setT : int -> tactic
val eqcd_setT : tactic

(* Hiding and unhiding *)
val squashT : tactic
val unhideT : int -> tactic
val unhideAllT : tactic

(* Primitives *)
val is_set_term : term -> bool
val dest_set : term -> string * term * term
val mk_set_term : string -> term -> term -> term

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
