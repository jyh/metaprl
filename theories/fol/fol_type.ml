(*
 * Typehood in FOL.
 *)

include Base_theory

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

declare "type"{'A}
declare trivial

dform type_df : "type"{'A} = slot{'A} `" type"

dform trivial_df : trivial = cdot

let type_term = << "type"{'A} >>
let type_opname = opname_of_term type_term
let is_type_term = is_dep0_term type_opname
let mk_type_term = mk_dep0_term type_opname
let dest_type = dest_dep0_term type_opname

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
