(*
 * We implement the arith procedure in the Nuprl book on page 173.
 * We use our own data structures for the sequent, and the formulas
 * here.
 *)

include Itt_int

(*
 * H >- 'T
 * by arith
 *
 * This is computed with a side condition.
 *)
mlterm arith_check{'t}
axiom arith : arith_check{'t} --> 't


(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
