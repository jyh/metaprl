(*
 * "True" constant.
 *)

include Fol_type

declare "true"
declare "it"

dform true_df : "true" = `"True"

prim true_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{."true"} } = trivial

prim true_intro {| intro [] |} 'H :
   sequent ['ext] { 'H >- "true" } = it

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
