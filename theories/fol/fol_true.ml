(*
 * "True" constant.
 *)

extends Fol_type

open Dtactic

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
