(*
 * We need a rule for when rewrites are valid.
 *)

include Perv
include Base_dtactic

open Refiner.Refiner.Term

open Tactic_type

declare rewrite_just

axiom rewriteDone 'H : sequent { 'H >- "rewrite"{'x; 'x} }

val rewrite_term : term
val d_rewriteT : int -> tactic

(*
 * $Log$
 * Revision 1.2  1998/06/12 13:47:16  jyh
 * D tactic works, added itt_bool.
 *
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
