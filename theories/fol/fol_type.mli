(*
 * Typehood on FOL.
 *)

include Base_theory

open Refiner.Refiner.TermType

declare univ
declare prop{'t}
declare "type"{'A}
declare trivial

(*
val is_type_term : term -> bool
val mk_type_term : term -> term
val dest_type : term -> term
*)

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
