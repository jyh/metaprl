(*
 * Falsehood.
 *)
extends Fol_type

open Tactic_type
open Base_dtactic

declare "false"

dform false_df : except_mode[src] :: "false" = `"False"

prim false_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{."false"} } = trivial

prim false_elim {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; x: "false"; 'J['x] >- 'C['x] } = trivial

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
