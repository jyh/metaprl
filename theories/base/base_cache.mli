(*
 * Create the cache as a resource.
 *)

include Tactic_cache
include Tactic_type

open Refiner.Refiner

open Tactic_cache
open Tactic_type

type cache_rule =
   Forward of tactic frule
 | Backward of tactic brule

type cache = tactic Tactic_cache.cache

type t

resource (cache_rule, cache, t) cache_resource

(*
 * $Log$
 * Revision 1.3  1998/06/03 22:19:41  jyh
 * Nonpolymorphic refiner.
 *
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
