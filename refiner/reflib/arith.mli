(*
 *
 * Positive cycle search in a graph.
 * Used by itt_int_arith/arithT
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
 * Author: Yegor Bryukhov @email{ynb@mail.ru}
 * Modified by: Aleksey Nogin @email{nogin@cs.cornell.edu}
 *)

open Refiner.Refiner.TermType

val collect : (term -> bool) -> term -> int list

module TG :
sig
   type dist =
      Disconnected
    | Int of int * int list
   val solve : (term * int array) -> dist * dist array
end