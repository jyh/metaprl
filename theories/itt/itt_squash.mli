(*
 * We also define a resource to prove squash stability.
 * Terms are "squash stable" if their proof can be inferred from the
 * fact that they are true.  The general form is a squash
 * proof is just:
 *     sequent [it; squash] { H >> T } -->
 *     sequent [it; it] { H >> T }
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

include Base_theory
include Itt_comment

open Refiner.Refiner.Term

open Tactic_type.Sequent
open Tactic_type.Tacticals

(*
 * Internal type.
 *)
type squash_data

(*
 * The resource itself.
 *)
resource (term * tactic, tactic, squash_data, unit) squash_resource

(*
 * Access to resources from the toploop.
 *)
val get_resource : string -> squash_resource

(*
 * Utilities.
 *)
topval squashT : tactic

val is_squash_goal : tactic_arg -> bool
val is_squash_sequent : term -> bool
val get_squash_arg : term -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
