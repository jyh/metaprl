(*
 * Classical reasoning.
 *)

include Fol_not

open Tactic_type.Tacticals

declare magic{x. 't['x]}

val magicT : tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
