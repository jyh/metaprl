(*
 * Falsehood.
 *)
include Fol_type

open Nl_resource
open Base_dtactic
open Refiner.Refiner.RefineError

declare "false"

dform false_df : "false" = `"False"

prim false_type 'H : :
   sequent ['ext] { 'H >- "type"{."false"} } = trivial

prim false_elim 'H 'J : :
   sequent ['ext] { 'H; x: "false"; 'J['x] >- 'C['x] } = trivial

(*
 * Add to the dT tactic.
 *)
let d_false_type i p =
   if i = 0 then
      false_type (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_false_type", StringError "no elimination form"))

let false_type_term = << "type"{."false"} >>

let d_resource = d_resource.resource_improve d_resource (**)
                    (false_type_term, d_false_type)

let d_false i p =
   if i = 0 then
      raise (RefineError ("d_false_type", StringError "no introduction form"))
   else
      let j, k = Sequent.hyp_indices p i in
         false_elim j k p

let false_term = << "false" >>

let d_resource = d_resource.resource_improve d_resource (**)
                    (false_term, d_false)

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
