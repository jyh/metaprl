(*
 * Create the cache as a resource.
 *)

include Tactic_cache
include Tactic_type

open Refine

open Tactic_cache
open Tactic_type

type cache_rule =
   Forward of tactic_argument Refiner.tactic frule
 | Backward of tactic_argument Refiner.tactic brule

type cache = tactic_argument Refiner.tactic Tactic_cache.cache

type t

resource (cache_rule, cache, t) cache_resource

(*
 * $Log$
 * Revision 1.1  1998/05/07 16:02:57  jyh
 * Adding interactive proofs.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
