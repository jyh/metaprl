(*
 * "True" constant.
 *)

extends Fol_type

open Base_dtactic

declare "true"
declare "it"

dform true_df : "true" = `"True"

prim true_type {| intro [] |} :
   sequent ['ext] { 'H >- "type"{."true"} } = trivial

prim true_intro {| intro [] |} :
   sequent ['ext] { 'H >- "true" } = it

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
