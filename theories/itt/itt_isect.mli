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

extends Itt_equal
extends Itt_set
extends Itt_rfun
extends Itt_logic
extends Itt_struct2

open Refiner.Refiner.Term

open Tactic_type.Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "isect"{'A; x. 'B['x]}

rewrite unfold_top : top <--> "isect"{void; x. void}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext isect x: A. B[x]
 * by intersectionFormation x A
 * H >- A = A in Ui
 * H, x: A >- Ui ext B[x]
 *)
rule intersectionFormation 'x 'A :
   sequent [squash] { 'H >- 'A = 'A in univ[i:l] } -->
   sequent ['ext] { 'H; x: 'A >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H >- isect x1:A1. B1[x1] = isect x2:A2. B2[x2] in Ui
 * by intersectionEquality y
 * H >- A1 = A2 in Ui
 * H, y: A1 >- B1[y] = B2[y] in Ui
 *)
rule intersectionEquality 'y :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent ['ext] { 'H >- Isect x1: 'A1. 'B1['x1] = Isect x2: 'A2. 'B2['x2] in univ[i:l] }

rule intersectionType 'y :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- "type"{."isect"{'A; x. 'B['x]}} }

rule topUniv :
   sequent ['ext] { 'H >- top in univ[i:l] }

rule topType :
   sequent ['ext] { 'H >- "type"{top} }

(*
 * H >- isect x: A. B ext b[it]
 * by intersectionMemberFormation z
 * H >- A = A in type
 * H, z: squash(A) >- B ext b[z]

rule intersectionMemberFormation 'z :
    sequent [squash] { 'H >- "type"{'A} } -->
    sequent ['ext] { 'H; z: squash{'A} >- 'B } -->
    sequent ['ext] { 'H >- isect x: 'A. 'B }
 *)


(*
 * H >- b1 = b2 in isect x:A. B[x]
 * by intersectionMemberEquality z
 * H >- A = A in type
 * H, z: A >- b1 = b2 in B[z]
 *)
rule intersectionMemberEquality 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; z: 'A >- 'b1 = 'b2 in 'B['z] } -->
   sequent ['ext] { 'H >- 'b1 = 'b2 in Isect x: 'A. 'B['x] }

rule topMemberEquality :
   sequent ['ext] { 'H >- 'b1 = 'b2 in top }

(*
 * H >- b1 = b2 in B[a]
 * by intersectionMemberCaseEquality (Isect x:A. B[x]) a
 * H >- b1 = b2 in Isect x:A. B[x]
 * H >- a = a in A
 *)
rule intersectionMemberCaseEquality (Isect x: 'A. 'B['x]) 'a :
   sequent [squash] { 'H >- 'b1 = 'b2 in Isect x: 'A. 'B['x] } -->
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'b1 = 'b2 in 'B['a] }


(*
 * H >- Isect a1:A1. B1 <= Isect a2:A2. B2
 * by intersectionSubtype
 *
 * H >- A2 <= A1
 * H, a: A2 >- B1[a] <= B2[a]
 *)
rule intersectionSubtype 'a :
   sequent [squash] { 'H >- \subtype{'A2; 'A1} } -->
   sequent [squash] { 'H; a: 'A2 >- \subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { 'H >- \subtype{ (Isect a1:'A1. 'B1['a1]); (Isect a2:'A2. 'B2['a2]) } }

rule topSubtype :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent ['ext] { 'H >- \subtype{'T; top} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

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
