(*
 * Define a cache resource.
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

include Tactic_cache
include Summary

open Refiner.Refiner
open Mp_resource

open Tactic_cache
open Tactic_type.Tacticals

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

type cache_rule =
   Forward of tactic frule
 | Backward of tactic brule

type cache = tactic Tactic_cache.cache

(*
 * Our "abstract" type is just a cache.
 *)
type t = cache

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Add a rule.
 *)
let improve_data info cache =
   match info with
      Forward info ->
         add_frule cache info
    | Backward info ->
         add_brule cache info

(*
 * Wrap up the joiner.
 *)
let join_resource = join_cache

let extract_resource data = data

let improve_resource data x =
   improve_data x data

let close_resource rsrc modname =
   rsrc

(*
 * Resource.
 *)
let resource cache = {
   resource_empty = new_cache ();
   resource_join = join_resource;
   resource_extract = extract_resource;
   resource_improve = improve_resource;
   resource_improve_arg = Mp_resource.improve_arg_fail "cache_resource";
   resource_close = close_resource
}

let get_resource modname =
   Mp_resource.find cache_resource modname

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
