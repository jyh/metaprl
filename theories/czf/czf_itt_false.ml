(*
 * Logical false.
 *)

include Czf_itt_set

open Refiner.Refiner.RefineError

open Sequent
open Resource
open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "false"

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform false_df : "false" =
   `"false'"

(************************************************************************
 * DEFINTION                                                            *
 ************************************************************************)

primrw unfold_false : "false" <--> void

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * From false prove anything.
 *
 * H, x: false, J >> T
 * by false_elim i
 *)
interactive false_elim 'H 'J : :
   sequent ['ext] { 'H; x: "false"; 'J['x] >- 'T['x] }

(*
 * False is well-formed.
 *)
interactive false_wf 'H : :
   sequent ['ext] { 'H >- wf{."false"} }

(*
 * False is a type.
 *)
interactive false_type 'H : :
   sequent ['ext] { 'H >- "type"{."false"} }

(*
 * False is a restricted formula.
 *)
interactive false_res 'H : :
   sequent ['ext] { 'H >- restricted{x ."false"} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let false_term = << "false" >>
let wf_false_term = << wf{."false"} >>
let res_false_term = << restricted{."false"} >>

(*
 * Falsehood.
 *)
let d_falseT i p =
   (if i = 0 then
      idT
   else
      let i, j = hyp_indices p i in
         false_elim i j) p

let d_resource = d_resource.resource_improve d_resource (false_term, d_falseT)

(*
 * Well-formedness.
 *)
let d_wf_falseT i p =
   if i = 0 then
      false_wf (hyp_count p) p
   else
      raise (RefineError ("d_wf_falseT", (StringTermError ("no elim form", wf_false_term))))

let d_resource = d_resource.resource_improve d_resource (wf_false_term, d_wf_falseT)

(*
 * False is a type.
 *)
let d_false_typeT i p =
   if i = 0 then
      false_type (hyp_count p) p
   else
      raise (RefineError ("d_false_typeT", (StringError "no elimination form")))

let false_type_term = << "type"{."false"} >>

let d_resource = d_resource.resource_improve d_resource (false_type_term, d_false_typeT)

(*
 * Restricted.
 *)
let d_res_falseT i p =
   if i = 0 then
      false_res (hyp_count p) p
   else
      raise (RefineError ("d_res_falseT", (StringTermError ("no elim form", res_false_term))))

let d_resource = d_resource.resource_improve d_resource (res_false_term, d_res_falseT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)

