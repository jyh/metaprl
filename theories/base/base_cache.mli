(*
 * Create the cache as a resource.
 *)

include Tactic_cache
include Tacticals

open Refiner.Refiner

open Tactic_cache
open Tacticals

type cache_rule =
   Forward of tactic frule
 | Backward of tactic brule

type cache = tactic Tactic_cache.cache

type t

resource (cache_rule, cache, t) cache_resource

(*
 * Access to caches for toploop.
 *)
val get_resource : string -> cache_resource

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
