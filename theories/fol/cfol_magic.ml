(*
 * Classical reasoning.
 *)
extends Fol_not

open Tactic_type

declare magic{x. 't['x]}

dform magic_df : magic {x. 't} = `"magic"

prim magic 'x :
   ('t['x] : sequent ['ext] { 'H; x: "not"{'T} >- "false" }) -->
   sequent ['ext] { 'H >- 'T } =
   magic{x. 't['x]}

let magicT p =
   let v = Var.maybe_new_vars1 p "v" in
      magic v p

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
