(*
 * Subtype type.
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

include Itt_equal

open Refiner.Refiner.Term

open Sequent
open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare subtype{'A; 'B}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_subtype

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext subtype(A; B)
 * by subtypeFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
axiom subtypeFormation 'H :
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- subtype(A1; B1) = subtype(A2; B2) in Ui
 * by subtypeEquality
 *
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
axiom subtypeEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- subtype{'A1; 'B1} = subtype{'A2; 'B2} in univ[@i:l] }

axiom subtypeType 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{subtype{'A; 'B}} }

axiom subtypeTypeLeft 'H 'A :
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- "type"{'B} }

axiom subtypeTypeRight 'H 'B :
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- "type"{'A} }

(*
 * H >- subtype(A; B) ext it
 * by subtype_axiomFormation
 *
 * H >- A = A in Ui
 * H; x: A; y: A; x = y in A >- x = y in B
 *)
axiom subtype_axiomFormation 'H 'x :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'A >- 'x = 'x in 'B } -->
   sequent ['ext] { 'H >- subtype{'A; 'B} }

(*
 * H >- it = it in subtype(A; B)
 * by subtype_axiomEquality
 *
 * H >- subtype(A; B)
 *)
axiom subtype_axiomEquality 'H :
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- it = it in subtype{'A; 'B} }

(*
 * H, x: subtype(A; B); J[x] >- C[x]
 * by subtypeElimination
 *
 * H, x: subtype(A; B); J[it] >- C[it]
 *)
axiom subtypeElimination 'H 'J :
   sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J['x] >- 'C['x] }

(*
 * H >- x = y in B
 * by subtypeElimination2 A
 *
 * H >- x = y in A
 * H >- subtype(A; B)
 *)
axiom subtypeElimination2 'H 'J 'a 'y :
   sequent [squash] { 'H; x: subtype{'A; 'B}; 'J['x] >- member{'A; 'a} } -->
   sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J['x]; y: member{'B; 'a} >- 'C['x] } -->
   sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J['x] >- 'C['x] }

(*
 * Squash elimination.
 *)
axiom subtype_squashElimination 'H :
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- subtype{'A; 'B} }

(************************************************************************
 * RESOURCE                                                             *
 ************************************************************************)

(*
 * Define a resource to keep track of proofs of subtyping.
 * This resource provides tactics to prove subtyping goals.
 * These tactics take transitivity into account, and try
 * to construct an optimal subtype chain.
 *)

(*
 * This is what is supplied to the resource.
 *)
type sub_info_type = (term * term) list * tactic

type sub_resource_info =
   LRSubtype of sub_info_type
 | RLSubtype of sub_info_type
 | DSubtype of sub_info_type

(*
 * Internal type.
 *)
type sub_data

(*
 * The resource itself.
 *)
resource (sub_resource_info, tactic, sub_data) sub_resource

(*
 * Access to resources from the toploop.
 *)
val get_resource : string -> sub_resource

(*
 * Utilities.
 *)
topval subtypeT : tactic

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval d_subtypeT : int -> tactic
topval eqcd_subtype : tactic

val is_subtype_term : term -> bool
val dest_subtype : term -> term * term
val mk_subtype_term : term -> term -> term

topval squash_subtypeT : tactic
topval type_subtype_leftT : term -> tactic
topval type_subtype_rightT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
