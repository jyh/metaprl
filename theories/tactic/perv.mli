(*
 * These are the public pervasive terms.
 *)

declare "nil"
declare "cons"{'car; 'cdr}
declare "string"[@s:s]
declare "lambda"{x. 'b}
declare "hyp"{'A; x. 'B}
declare "concl"{'A; 'B}
(* declare "sequent"{'ext; 'A} *)
declare "rewrite"{'redex; 'contractum}

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
