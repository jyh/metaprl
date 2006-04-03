(*
 * Some utilities for simplifying the reflection theory.
 * These should eventually be migrated into the reflection
 * theory proper as necessary.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005-2006 Mojave Group, Caltech
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
 * Author: Jason Hickey @email{jyh@cs.caltech.edu}
 * Modified by: Aleksey Nogin @email{nogin@cs.caltech.edu}
 * @end[license]
 *)
open Basic_tactics

extends Itt_hoas_bterm

(*
 * Error term.
 *)
declare Invalid_argument

(*
 * A "dummy" term.
 *)
declare dummy_bterm

(*
 * Rewrite annotation processor with arithmetical simplifier
 *)
val arith_rw_annotation : string -> (term * conv) rw_annotation_processor

(*
 * Tell forward to run reduceC on the type part of the equality hyp
 *)
val fwd_reduce_type : int -> forward_option
