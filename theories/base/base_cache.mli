(*
 * Create the cache as a resource.
 *)

include Tactic_cache
include Tactic_type

open Refiner.Refiner

open Tactic_cache
open Tactic_type

type cache_rule =
   Forward of tactic_argument Refine.tactic frule
 | Backward of tactic_argument Refine.tactic brule

type cache = tactic_argument Refine.tactic Tactic_cache.cache

type t

resource (cache_rule, cache, t) cache_resource

(*
 * $Log$
 * Revision 1.2  1998/05/28 13:47:11  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
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
