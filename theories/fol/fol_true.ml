(*
 * "True" constant.
 *)

extends Fol_type

open Basic_tactics

declare "true"
declare "it"

dform true_df : "true" = `"True"

prim true_type {| intro [] |} :
   sequent { <H> >- "type"{."true"} } = trivial

prim true_intro {| intro [] |} :
   sequent { <H> >- "true" } = it

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
