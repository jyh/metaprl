(*
 * Universal quantifier.
 *)

include Fol_implies
include Fol_univ

declare "all"{x. 'B['x]}

prec prec_all

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
