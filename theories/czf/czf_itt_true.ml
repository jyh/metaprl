(*
 * Logical true.
 *)

include Czf_itt_wf

open Refiner.Refiner.Refine

open Sequent
open Resource
open Tacticals

declare "true"

primrw unfoldTrue : "true" <--> (0 = 0 in int)

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform true_df : "true" =
   `"true"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * True is always true.
 *
 * H >- true
 * by true_intro
 *)
prim true_intro 'H : : sequent ['ext] { 'H >- "true" } =
   it

(*
 * True is well formed.
 *
 * H >- wf{"true"}
 * by true_wf
 *)
prim true_wf 'H : :
   sequent ['ext] { 'H >- wf{."true"} } =
   it

(*
 * True is a restricted formula.
 *)
prim true_res 'H : :
   sequent ['ext] { 'H >- restricted{."true"} } =
   it

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
 * Restricted.
 *)
let d_res_trueT i p =
   if i = 0 then
      true_res (hyp_count p) p
   else
      raise (RefineError ("d_res_trueT", (StringTermError ("no elim form", res_true_term))))

let d_resource = d_resource.resource_improve d_resource (res_true_term, d_res_trueT)

(*
 * $Log$
 * Revision 1.2  1998/06/16 16:26:06  jyh
 * Added itt_test.
 *
 * Revision 1.1  1998/06/15 22:32:52  jyh
 * Added CZF.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
