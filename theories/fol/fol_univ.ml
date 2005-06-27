(*
 * Type universes.
 *)

extends Fol_type

open Basic_tactics

declare univ
declare prop{'t}

dform univ_df : univ = `"Univ"
dform prop_df : prop{'t} = downarrow slot{'t}

prim univ_type {| intro [] |} 'H :
   sequent { <H>; x: univ; <J['x]> >- "type"{prop{'x}} } =
   trivial

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
