(*
 * Logical true.
 *)

include Czf_itt_set

open Refiner.Refiner.RefineError

open Sequent
open Resource
open Tacticals

declare "true"

primrw unfold_true : "true" <--> unit

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform true_df : "true" =
   `"true'"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * True is always true.
 *
 * H >- true
 * by true_intro
 *)
interactive true_intro 'H : : sequent ['ext] { 'H >- "true" }

(*
 * True is well formed.
 *
 * H >- wf{"true"}
 * by true_wf
 *)
interactive true_wf 'H : :
   sequent ['ext] { 'H >- wf{."true"} }

(*
 * Typehood.
 *)
interactive true_type 'H : :
   sequent ['ext] { 'H >- "type"{."true"} }

(*
 * True is a restricted formula.
 *)
interactive true_res 'H : :
   sequent ['ext] { 'H >- restricted{x ."true"} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let true_term = << "true" >>
let wf_true_term = << wf{."true"} >>
let res_true_term = << restricted{."true"} >>

(*
 * Truth.
 *)
let d_trueT i p =
   (if i = 0 then
       true_intro (hyp_count p)
    else
       idT) p

let d_resource = d_resource.resource_improve d_resource (true_term, d_trueT)

(*
 * Well-formedness.
 *)
let d_wf_trueT i p =
   if i = 0 then
      true_wf (hyp_count p) p
   else
      raise (RefineError ("d_wf_trueT", (StringTermError ("no elim form", wf_true_term))))

let d_resource = d_resource.resource_improve d_resource (wf_true_term, d_wf_trueT)

(*
 * Typehood.
 *)
let d_true_typeT i p =
   if i = 0 then
      true_type (hyp_count p) p
   else
      raise (RefineError ("d_true_typeT", (StringError "no elimination form")))

let true_type_term = << "type"{."true"} >>

let d_resource = d_resource.resource_improve d_resource (true_type_term, d_true_typeT)

(*
 * Restricted.
 *)
let d_res_trueT i p =
   if i = 0 then
      true_res (hyp_count p) p
   else
      raise (RefineError ("d_res_trueT", (StringTermError ("no elim form", res_true_term))))

let d_resource = d_resource.resource_improve d_resource (res_true_term, d_res_trueT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
