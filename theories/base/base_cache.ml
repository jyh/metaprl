(*
 * Define a cache resource.
 *)

include Tactic_cache
include Tactic_type

open Refiner.Refiner
open Resource

open Tactic_cache
open Tactic_type

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

type cache_rule =
   Forward of tactic_argument Refine.tactic frule
 | Backward of tactic_argument Refine.tactic brule

type cache = tactic_argument Refine.tactic Tactic_cache.cache

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
 * Wrap up the joiner.
 *)
let rec join_resource base1 base2 =
   let data = join_cache base1.resource_data base2.resource_data in
      { resource_data = data;
        resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource
      }
      
and extract_resource { resource_data = data } =
   data
   
and improve_resource { resource_data = data } x =
   { resource_data = improve_data x data;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * Resource.
 *)
let cache_resource =
   { resource_data = new_cache ();
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

let cache = cache_resource.resource_extract cache_resource

(*
 * $Log$
 * Revision 1.2  1998/05/28 13:47:09  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.1  1998/05/07 16:02:55  jyh
 * Adding interactive proofs.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
