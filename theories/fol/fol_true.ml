(*
 * "True" constant.
 *)

include Fol_type

open Mp_resource
open Refiner.Refiner.RefineError

declare "true"
declare "it"

dform true_df : "true" = `"True"

prim true_type {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "type"{."true"} } = trivial

prim true_intro {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "true" } = it

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
