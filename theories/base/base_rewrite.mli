(*
 * We need a rule for when rewrites are valid.
 *)

include Perv

declare rewrite_just

axiom rewriteDone 'H : sequent { 'H >- "rewrite"{'x; 'x} }

(*
 * $Log$
 * Revision 1.1  1998/06/01 19:53:58  jyh
 * Working addition proof.  Removing polymorphism from refiner(?)
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
