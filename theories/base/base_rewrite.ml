(*
 * We need a rule for when rewrites are valid.
 *)

include Perv
include Base_dtactic

open Resource
open Refiner.Refiner.Refine

declare rewrite_just

prim rewriteDone 'H : : sequent { 'H >- "rewrite"{'x; 'x} } =
   rewrite_just

(*
 * Template for the term.
 *)
let rewrite_term = << "rewrite"{'a; 'b} >>

(*
 * The dtactic operation only works on a concl.
 *)
let d_rewriteT i p =
   if i = 0 then
      rewriteDone (Sequent.hyp_count p) p
   else
      raise (RefineError ("d_rewriteT", StringError "can't decompose a rewrite hyp"))

let d_resource = d_resource.resource_improve d_resource (rewrite_term, d_rewriteT)

(*
 * $Log$
 * Revision 1.2  1998/06/12 13:47:15  jyh
 * D tactic works, added itt_bool.
 *
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
