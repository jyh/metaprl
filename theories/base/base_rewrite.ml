(*
 * We need a rule for when rewrites are valid.
 *)

include Perv

declare rewrite_just

prim rewriteDone 'H : : sequent { 'H >- "rewrite"{'x; 'x} } =
   rewrite_just                          

(*
 * $Log$
 * Revision 1.1  1998/06/01 19:53:56  jyh
 * Working addition proof.  Removing polymorphism from refiner(?)
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
