(*
 * Logical true.
 *)

include Czf_itt_sep

open Printf
open Nl_debug

open Refiner.Refiner.RefineError

open Sequent
open Resource
open Tacticals

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_true%t" eflush

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * True is functional.
 *)
interactive unit_fun 'H : :
   sequent ['ext] { 'H >- fun_prop{z. "unit"} }

(*
 * True is a restricted formula.
 *)
interactive unit_res 'H : :
   sequent ['ext] { 'H >- restricted{z. "unit"} }

(*
 * True is a restricted formula.
 *)
interactive true_fun 'H : :
   sequent ['ext] { 'H >- fun_prop{x. "true"} }

(*
 * True is a restricted formula.
 *)
interactive true_res 'H : :
   sequent ['ext] { 'H >- restricted{x. "true"} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Restricted.
 *)
let d_true_funT i p =
   if i = 0 then
      true_fun (hyp_count p) p
   else
      raise (RefineError ("d_true_funT", StringError "no elimination form"))

let true_fun_term = << fun_prop{x. "true"} >>

let d_resource = d_resource.resource_improve d_resource (true_fun_term, d_true_funT)

(*
 * Restricted.
 *)
let d_true_resT i p =
   if i = 0 then
      true_res (hyp_count p) p
   else
      raise (RefineError ("d_true_resT", StringError "no elimination form"))

let true_res_term = << restricted{x. "true"} >>

let d_resource = d_resource.resource_improve d_resource (true_res_term, d_true_resT)

(*
 * Restricted.
 *)
let d_unit_funT i p =
   if i = 0 then
      unit_fun (hyp_count p) p
   else
      raise (RefineError ("d_unit_funT", StringError "no elimination form"))

let unit_fun_term = << fun_prop{x. "unit"} >>

let d_resource = d_resource.resource_improve d_resource (unit_fun_term, d_unit_funT)

(*
 * Restricted.
 *)
let d_unit_resT i p =
   if i = 0 then
      unit_res (hyp_count p) p
   else
      raise (RefineError ("d_unit_resT", StringError "no elimination form"))

let unit_res_term = << restricted{x. "unit"} >>

let d_resource = d_resource.resource_improve d_resource (unit_res_term, d_unit_resT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
