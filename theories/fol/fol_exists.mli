(*
 * Existential quantifier.
 *)

extends Fol_and
extends Fol_pred

declare "exists"{x. 'B['x]}

prec prec_exists

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
