(*
 * This module defines the squish operator that hides witnesses
 * of a proposition. It also shows a relation between the type
 * theory squash operator and a meta-theory sequent squash operation.
 *
 * We also define a resource to prove squash stability.
 * Terms are "squash stable" if their proof can be inferred from the
 * fact that they are true.
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
 * Authors:
 *    Jason Hickey <jyh@cs.cornell.edu>
 *    Alexei Kopylov <kopylov@cs.cornell.edu>
 *    Aleksey Nogin <nogin@cs.cornell.edu>
 *)

include Itt_equal
include Itt_struct

open Refiner.Refiner.Term

open Tactic_type
open Tactic_type.Sequent
open Tactic_type.Tacticals
open Mp_resource

declare squash{'A}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)


rule squashEquality 'H  :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   sequent ['ext] { 'H >- squash{'A1} = squash{'A2} in univ[i:l] }

rule squashType 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{squash{'A}} }

rule squashMemberFormation 'H :
   sequent [squash] { 'H >- 'A } -->
   sequent ['ext]   { 'H >- squash{'A} }

rule squashElim 'H 'J :
   sequent ['ext] { 'H; u: squash{'P}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; u: squash{'P}; 'J['u] >- 'C['u] }

rule unsquashEqual 'H 'J :
   sequent [squash] { 'H; u: 'P; 'J[it] >- 'x[it] = 'y[it] in 'A[it] } -->
   sequent ['ext] { 'H; u: squash{'P}; 'J['u] >- 'x['u] = 'y['u] in 'A['u] }

rule squashFromAny 'H 'ext :
   sequent ['ext] { 'H >- 'T } -->
   sequent [squash] { 'H >- 'T }

rule squashMemberEquality 'H :
   [wf] sequent [squash] { 'H >- squash{'A} } -->
   sequent ['ext] { 'H >- it IN squash{'A} }

rule squashStable 'H 't :
   [main] sequent [squash] { 'H >- squash{'A} } -->
   [wf] sequent [squash] { 'H; x: 'A >- 't IN 'A } -->
   sequent ['ext] { 'H >- 'A}

rule unsquashHypEqual 'H 'J :
   sequent ['ext] { 'H; u: 'x = 'y in 'A; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; u: squash{('x = 'y in 'A)}; 'J['u] >- 'C['u] }

rule unsquash 'H 'J :
   sequent [squash] { 'H; u: 'P; 'J[it] >- squash{'T[it]} } -->
   sequent ['ext] { 'H; u: squash{'P}; 'J['u] >- squash{'T['u]} }

(*
 * H >- Ui ext squash(A)
 * by squashFormation
 * H >- Ui ext A
 *)
rule squashFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(* Primitives *)
val is_squash_term : term -> bool
val dest_squash : term -> term
val mk_squash_term : term -> term

(*
 * Internal type.
 *)
type squash_info
type squash_data

(*
 * The resource itself.
 *)
resource (squash_info, squash_data, int -> tactic) squash

val process_squash_resource_annotation :
   (Tactic.pre_tactic, squash_info) annotation_processor

(*
 * Utilities.
 *)
val is_squash_goal : tactic_arg -> bool
val is_squash_sequent : term -> bool
val get_squash_arg : term -> term

(* Squashing and unsquashing *)
topval squashT : tactic
topval unsquashT : int -> tactic
topval unsquashAllT : tactic

(* Sequent squash *)
topval sqsquashT : tactic
topval unsqsquashT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
