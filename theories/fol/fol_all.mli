(*
 * Universal quantifier.
 *)

extends Fol_implies
extends Fol_struct
extends Fol_pred

declare "all"{x. 'B['x]}

prec prec_all

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
