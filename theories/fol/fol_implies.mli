(*
 * Implication.
 *)

extends Fol_type

prec prec_implies
prec prec_lambda
prec prec_apply

declare implies{'A; 'B}
declare lambda{x. 'b['x]}
declare apply{'f; 'a}

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
