(*
 * The D tactic performs a case selection on the conclusion opname.
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

include Base_auto_tactic

open Refiner.Refiner.Term
open Refiner.Refiner.Refine
open Tacticals

open Base_auto_tactic

(*
 * This are the types.
 *)
type d_data

resource (term * (int -> tactic), int -> tactic, d_data, meta_term * tactic) d_resource

(*
 * Get a resource for the toploop.
 *)
val get_resource : string -> d_resource

val add_d_info : d_resource -> (term * (int -> tactic)) list -> d_resource

(*
 * The inherited d tactic.
 *)
val d_prec : auto_prec

topval dT : int -> tactic

(*
 * Run dT 0 so many times.
 *)
topval dForT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
