(*
 * Falsehood.
 *)
include Fol_type

open Mp_resource
open Base_dtactic
open Refiner.Refiner.RefineError

declare "false"

dform false_df : "false" = `"False"

prim false_type {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "type"{."false"} } = trivial

prim false_elim {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; x: "false"; 'J['x] >- 'C['x] } = trivial

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
