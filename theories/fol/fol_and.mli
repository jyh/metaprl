(*
 * Conjunction.
 *)

include Fol_type

declare "and"{'A; 'B}
declare "pair"{'a; 'b}
declare "spread"{'x; a, b. 'body['a; 'b]}

prec prec_and

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
