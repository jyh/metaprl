(*
 * Utilities for generating variable names.
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

open Tactic_type.Sequent

(* Generate a new var different from any in the list *)
val new_var         : string -> string list -> string
val maybe_new_var   : string -> string list -> string
val maybe_new_vars  : string list -> string list -> string list

val maybe_new_vars_array : tactic_arg -> string array -> string array
val maybe_new_vars1 : tactic_arg -> string -> string
val maybe_new_vars2 : tactic_arg -> string -> string -> string * string
val maybe_new_vars3 : tactic_arg -> string -> string -> string -> string * string * string
val maybe_new_vars4 : tactic_arg -> string -> string -> string -> string -> string * string * string * string
val maybe_new_vars5 : tactic_arg -> string -> string -> string -> string -> string -> string * string * string * string * string
val maybe_new_vars6 : tactic_arg -> string -> string -> string -> string -> string -> string -> string * string * string * string * string * string
val maybe_new_vars7 : tactic_arg -> string -> string -> string -> string -> string -> string -> string -> string * string * string * string * string * string * string
val maybe_new_vars8 : tactic_arg -> string -> string -> string -> string -> string -> string -> string -> string -> string * string * string * string * string * string * string * string
val maybe_new_vars9 : tactic_arg -> string -> string -> string -> string -> string -> string -> string -> string -> string -> string * string * string * string * string * string * string * string * string

val get_opt_var_arg : string -> tactic_arg -> string

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
