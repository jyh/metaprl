(*
 * Disjunction.
 *)

include Fol_type

declare "or"{'A; 'B}
declare inl{'a}
declare inr{'b}
declare decide{'x; y. 'body1['y]; z. 'body2['z]}

prec prec_or
prec prec_inl
prec prec_inr
prec prec_decide

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
