(*
 * "True" constant.
 *)

include Fol_type

open Nl_resource
open Refiner.Refiner.RefineError

declare "true"
declare "it"

dform true_df : "true" = `"True"

prim true_type 'H : :
   sequent ['ext] { 'H >- "type"{."true"} } = trivial

prim true_intro 'H : :
   sequent ['ext] { 'H >- "true" } = it

(*
 * Implement the d_resource.
 *)
let d_true_type i p =
   if i = 0 then
      true_type (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_true_type", StringError "no elimination form"))

let true_type_term = << "type"{."true"} >>

let d_resource = d_resource.resource_improve d_resource (true_type_term, d_true_type)

let d_true i p =
   if i = 0 then
      true_intro (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_true", StringError "no elimination form"))

let true_term = << "true" >>

let d_resource = d_resource.resource_improve d_resource (true_term, d_true)

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
