(*
 * Falsehood.
 *)
extends Fol_type

open Dtactic

declare "false"

dform false_df : except_mode[src] :: "false" = `"False"

prim false_type {| intro [] |} :
   sequent { <H> >- "type"{."false"} } = trivial

prim false_elim {| elim [] |} 'H :
   sequent { <H>; x: "false"; <J['x]> >- 'C['x] } = trivial

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
