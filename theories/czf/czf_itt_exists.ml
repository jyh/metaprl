(*
 * Primitiva interactiveatization of implication.
 *)

include Czf_itt_sep

open Printf
open Debug

open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Conversionals
open Sequent
open Var

open Base_auto_tactic
open Base_dtactic

open Itt_equal
open Itt_logic
open Itt_rfun
open Itt_derive
open Itt_dprod

(*
 * We need the allAutoT tactic from Czf_itt_all,
 * but we don't need the logic.
 *)
open Czf_itt_all

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_and%t" eflush

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Implication is restricted.
 *)
interactive dprod_fun3 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'A['z]} } -->
   sequent ['ext] { 'H >- dfun_prop{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- fun_prop{z. "prod"{'A['z]; w. 'B['z; 'w]}} }

interactive dprod_res3 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- restricted{z. "prod"{'A['z]; w. 'B['z; 'w]}} }

interactive exists_fun 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'A['z]} } -->
   sequent ['ext] { 'H >- dfun_prop{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- fun_prop{z. "exists"{'A['z]; w. 'B['z; 'w]}} }

interactive exists_res 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- restricted{z. "exists"{'A['z]; w. 'B['z; 'w]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * All rules have the same kind of hyps.
 *)
let labels =
   [addHiddenLabelT "wf";
    addHiddenLabelT "wf";
    addHiddenLabelT "main";
    addHiddenLabelT "main"]

(*
 * Functionality.
 *)
let d_dprod_funT i p =
   if i = 0 then
      let u, v, z = maybe_new_vars3 p "u" "v" "z" in
         (dprod_fun3 (hyp_count p) u v z thenLT labels) p
   else
      raise (RefineError ("d_dprod_funT", StringError "no elimination fandm"))

let dprod_fun_term = << fun_prop{z. "prod"{'P1['z]; w. 'P2['z; 'w]}} >>

let d_resource = d_resource.resource_improve d_resource (dprod_fun_term, d_dprod_funT)

(*
 * Restricted.
 *)
let d_dprod_resT i p =
   if i = 0 then
      let u, v, z = maybe_new_vars3 p "u" "v" "z" in
         (dprod_res3 (hyp_count p) u v z thenLT labels) p
   else
      raise (RefineError ("d_dprod_resT", StringError "no elimination fandm"))

let dprod_res_term = << restricted{z. "prod"{'P1['z]; w. 'P2['z; 'w]}} >>

let d_resource = d_resource.resource_improve d_resource (dprod_res_term, d_dprod_resT)

(*
 * Functionality.
 *)
let d_exists_funT i p =
   if i = 0 then
      let u, v, z = maybe_new_vars3 p "u" "v" "z" in
         (exists_fun (hyp_count p) u v z thenLT labels) p
   else
      raise (RefineError ("d_exists_funT", StringError "no elimination fandm"))

let exists_fun_term = << fun_prop{z. "exists"{'P1['z]; w. 'P2['z; 'w]}} >>

let d_resource = d_resource.resource_improve d_resource (exists_fun_term, d_exists_funT)

(*
 * Restricted.
 *)
let d_exists_resT i p =
   if i = 0 then
      let u, v, z = maybe_new_vars3 p "u" "v" "z" in
         (exists_res (hyp_count p) u v z thenLT labels) p
   else
      raise (RefineError ("d_exists_resT", StringError "no elimination fandm"))

let exists_res_term = << restricted{z. "exists"{'P1['z]; w. 'P2['z; 'w]}} >>

let d_resource = d_resource.resource_improve d_resource (exists_res_term, d_exists_resT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
