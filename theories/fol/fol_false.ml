(*
 * Falsehood.
 *)
include Fol_type

open Tactic_type

declare "false"

dform false_df : "false" = `"False"

prim false_type 'H :
   sequent ['ext] { 'H >- "type"{."false"} } = trivial

let d_false_type p =
   false_type (Sequent.hyp_count_addr p) p

let intro_resource = Mp_resource.improve intro_resource (<< "type"{."false"} >>, d_false_type)

prim false_elim 'H 'J :
   sequent ['ext] { 'H; x: "false"; 'J['x] >- 'C['x] } = trivial

let d_false_elim i p =
   let j, k = Sequent.hyp_indices p i in
      false_elim j k p

let elim_resource = Mp_resource.improve elim_resource (<< "false" >>, d_false_elim)

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
