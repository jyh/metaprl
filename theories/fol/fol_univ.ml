(*
 * Type universes.
 *)

extends Fol_type

open Mp_resource

open Tactic_type
open Tactic_type.Tacticals

open Auto_tactic

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
