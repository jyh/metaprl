(*
 * Create tables for success/failure/cycle-detection
 * caches.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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

open String_set

open Refiner.Refiner.TermType

(*
 * Compare two terms, given a set of constants.
 *)
val sort_term_list : term list -> term list
val merge_term_lists : term list -> term list -> term list

module TptpCache :
sig
   (*
    * Type of caches.
    *)
   type t

   (*
    * The strings are the function and predicate symbols in
    * the logic.
    *)
   val create : StringSet.t -> t

   (*
    * A clause is "subsumed" when an existing entry is
    * found that has a subset of the clause in the
    * argument.
    *)
   val subsumed : t -> term list -> bool

   (*
    * Add a new clause to the table.
    * This is functional, and it is assumed
    * that the clause is not already in the
    * table.  This operation is functional.
    *)
   val insert : t -> term list -> t
end

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
