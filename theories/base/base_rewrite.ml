(*
 * We need a rule for when rewrites are valid.
 *)

include Rewrite_type
include Base_dtactic

open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Rewrite_type

(*
 * Template for the term.
 *)
let rewrite_term = << "rewrite"{'a; 'b} >>

(*
 * The dtactic operation only works on a concl.
 *)
let d_rewriteT i p =
   if i = 0 then
      rewriteSequentAxiom (Sequent.hyp_count p) p
   else
      raise (RefineError ("d_rewriteT", StringError "can't decompose a rewrite hyp"))

let d_resource = d_resource.resource_improve d_resource (rewrite_term, d_rewriteT)

(*
 * $Log$
 * Revision 1.5  1998/07/02 18:36:48  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.4  1998/07/01 04:37:15  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.3  1998/06/22 19:46:02  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
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
