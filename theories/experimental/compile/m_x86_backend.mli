(*
 * Architecture-specific code for the backend.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
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
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends M_x86_term
extends M_ra_type

open Format

open Lm_symbol

open Refiner.Refiner.TermType

open M_ra_type

module Frame : FrameSig

(*
 * A variable renamer.
 *)
type rename = var SymbolTable.t

(*
 * Get all the vars that should be renamed.
 *)
val rename_term : term -> rename

(*
 * Helper functions.
 *)
val rename_find : rename -> var -> var

(*
 * Print the program.
 *)
val pp_print_prog : formatter -> term -> unit

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
