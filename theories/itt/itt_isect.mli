(*
 * Intersection type.
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
 *
 *)

include Tacticals

include Itt_equal
include Itt_set
include Itt_rfun
include Itt_logic

open Refiner.Refiner.Term

open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "isect"{'A; x. 'B['x]}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext isect x: A. B[x]
 * by intersectionFormation x A
 * H >- A = A in Ui
 * H, x: A >- Ui ext B[x]
 *)
rule intersectionFormation 'H 'x 'A :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   sequent ['ext] { 'H; x: 'A >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- isect x1:A1. B1[x1] = isect x2:A2. B2[x2] in Ui
 * by intersectionEquality y
 * H >- A1 = A2 in Ui
 * H, y: A1 >- B1[y] = B2[y] in Ui
 *)
rule intersectionEquality 'H 'y :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[@i:l] } -->
   sequent ['ext] { 'H >- isect x1: 'A1. 'B1['x1] = isect x2: 'A2. 'B2['x2] in univ[@i:l] }

rule intersectionType 'H 'y :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- "type"{."isect"{'A; x. 'B['x]}} }

(*
 * H >- isect x: A. B[x] ext b[it]
 * by intersectionMemberFormation z
 * H >- A = A in type
 * H, z: hide(A) >- B[z] ext b[z]
 *)
rule intersectionMemberFormation 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H; z: hide{'A} >- 'B['z] } -->
   sequent ['ext] { 'H >- isect x: 'A. 'B['x] }

(*
 * H >- b1 = b2 in isect x:A. B[x]
 * by intersectionMemberEquality z
 * H >- A = A in type
 * H, z: A >- b1 = b2 in B[z]
 *)
rule intersectionMemberEquality 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; z: 'A >- 'b1 = 'b2 in 'B['z] } -->
   sequent ['ext] { 'H >- 'b1 = 'b2 in isect x: 'A. 'B['x] }

(*
 * H >- b1 = b2 in B[a]
 * by intersectionMemberCaseEquality (isect x:A. B[x]) a
 * H >- b1 = b2 in isect x:A. B[x]
 * H >- a = a in A
 *)
rule intersectionMemberCaseEquality 'H (isect x: 'A. 'B['x]) 'a :
   sequent [squash] { 'H >- 'b1 = 'b2 in isect x: 'A. 'B['x] } -->
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'b1 = 'b2 in 'B['a] }

(*
 * H, x: isect y: A. B[y], J[x] >- T[x]
 * by intersectionElimination a z v
 * H, x: isect y: A. B[y], J[x] >- a = a in A
 * H, x: isect y: A. B[y], J[x], z: B[a], v: z = f in B[a] >- T[x]
 *)
rule intersectionElimination 'H 'J 'a 'x 'y 'v :
   sequent [squash] { 'H; x: isect y: 'A. 'B['y]; 'J['x] >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H; x: isect y: 'A. 'B['y]; 'J['x]; z: 'B['a]; v: 'z = 'x in 'B['a] >- 'T['x] } -->
   sequent ['ext] { 'H; x: isect y: 'A. 'B['y]; 'J['x] >- 'T['x] }

(*
 * H >- isect a1:A1. B1 <= isect a2:A2. B2
 * by intersectionSubtype
 *
 * H >- A2 <= A1
 * H, a: A1 >- B1[a] <= B2[a]
 *)
rule intersectionSubtype 'H 'a :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { 'H >- subtype{ (isect a1:'A1. 'B1['a1]); (isect a2:'A2. 'B2['a2]) } }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_isectT : int -> tactic
val eqcd_isectT : tactic

val is_isect_term : term -> bool
val dest_isect : term -> string * term * term
val mk_isect_term : string -> term -> term -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
