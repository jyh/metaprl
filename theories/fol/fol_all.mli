(*
 * Universal quantifier.
 *)

include Fol_implies
include Fol_struct
include Fol_pred

declare "all"{x. 'B['x]}

prec prec_all

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
