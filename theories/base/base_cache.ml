(*
 * Define a cache resource.
 *)

include Tactic_cache
include Tacticals

open Refiner.Refiner
open Nl_resource

open Tactic_cache
open Tacticals

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

resource (cache_rule, cache, t) cache_resource

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
 * Keep a list of resources for lookup by the toploop.
 *)
let resources = ref []

let save name rsrc =
   resources := (name, rsrc) :: !resources

let get_resource name =
   let rec search = function
      (name', rsrc) :: tl ->
         if name' = name then
            rsrc
         else
            search tl
    | [] ->
         raise Not_found
   in
      search !resources

(*
 * Wrap up the joiner.
 *)
let rec join_resource base1 base2 =
   let data = join_cache base1.resource_data base2.resource_data in
      { resource_data = data;
        resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource;
        resource_close = close_resource
      }

and extract_resource { resource_data = data } =
   data

and improve_resource { resource_data = data } x =
   { resource_data = improve_data x data;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource;
     resource_close = close_resource
   }

and close_resource rsrc modname =
   save modname rsrc;
   rsrc

(*
 * Resource.
 *)
let cache_resource =
   { resource_data = new_cache ();
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource;
     resource_close = close_resource
   }

let cache = cache_resource.resource_extract cache_resource

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
