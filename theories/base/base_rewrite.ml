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
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
