(*
 * Negation is defined in terms of implication.
 *)

include Fol_false
include Fol_implies

declare "not"{'A}

rewrite unfold_not : "not"{'A} <--> implies{'A; ."false"}

prec prec_not

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
