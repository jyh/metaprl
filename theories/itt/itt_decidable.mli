(*
 * decideT tactic and decide_resource to reason about decidable predicates.
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
 * Author: Aleksey Nogin
 * nogin@cs.cornell.edu
 *)

include Itt_logic

open Tactic_type
open Tactic_type.Tacticals
open Refiner.Refiner.TermType

define unfold_decidable : decidable{'p} <--> ('p or not {'p})

type decide_data

resource (term * tactic, tactic, decide_data, Tactic.pre_tactic ) decide

(* Works only on sequents of form "H |- Decidable(P)", tries to prove
   that P is in fact decidable using rules added to decide_resource *)
topval prove_decidableT : tactic

(* "decideT P" asserts decidability of P generating 3 subgoals -
   Decidable (P); case P; case not(P)
   that tries to eliminate the first subgoal using prove_decidableT *)
topval decideT : term -> tactic

