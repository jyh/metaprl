(*
 * Classical reasoning.
 *)
extends Fol_not

open Tactic_type

declare magic{x. 't['x]}

dform magic_df : magic {x. 't} = `"magic"

prim magic :
   ('t['x] : sequent ['ext] { <H>; x: "not"{'T} >- "false" }) -->
   sequent ['ext] { <H> >- 'T } =
   magic{x. 't['x]}

let magicT = magic

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
