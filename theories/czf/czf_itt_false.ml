(*
 * Logical false.
 *)

include Czf_itt_sep

open Printf
open Nl_debug

open Refiner.Refiner.RefineError

open Sequent
open Nl_resource
open Tacticals

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_false%t" eflush

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * False is a restricted formula.
 *)
interactive void_fun 'H : :
   sequent ['ext] { 'H >- fun_prop{x ."void"} }

(*
 * False is a restricted formula.
 *)
interactive void_res 'H : :
   sequent ['ext] { 'H >- restricted{x ."void"} }

(*
 * False is a restricted formula.
 *)
interactive false_fun 'H : :
   sequent ['ext] { 'H >- fun_prop{x ."false"} }

(*
 * False is a restricted formula.
 *)
interactive false_res 'H : :
   sequent ['ext] { 'H >- restricted{x ."false"} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Functional.
 *)
let d_void_funT i p =
   if i = 0 then
      void_fun (hyp_count_addr p) p
   else
      raise (RefineError ("d_void_funT", StringError "no elimination form"))

let void_fun_term = << fun_prop{z. "void"} >>

let d_resource = d_resource.resource_improve d_resource (void_fun_term, d_void_funT)

(*
 * Restricted.
 *)
let d_void_resT i p =
   if i = 0 then
      void_res (hyp_count_addr p) p
   else
      raise (RefineError ("d_void_resT", StringError "no elimination form"))

let void_res_term = << restricted{z. "void"} >>

let d_resource = d_resource.resource_improve d_resource (void_res_term, d_void_resT)

(*
 * Functional.
 *)
let d_false_funT i p =
   if i = 0 then
      false_fun (hyp_count_addr p) p
   else
      raise (RefineError ("d_false_funT", StringError "no elimination form"))

let false_fun_term = << fun_prop{z. "false"} >>

let d_resource = d_resource.resource_improve d_resource (false_fun_term, d_false_funT)

(*
 * Restricted.
 *)
let d_false_resT i p =
   if i = 0 then
      false_res (hyp_count_addr p) p
   else
      raise (RefineError ("d_false_resT", StringError "no elimination form"))

let false_res_term = << restricted{z. "false"} >>

let d_resource = d_resource.resource_improve d_resource (false_res_term, d_false_resT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)

