(*
 * Existential quantifier.
 *)

include Fol_and
include Fol_pred

declare "exists"{x. 'B['x]}

prec prec_exists

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
