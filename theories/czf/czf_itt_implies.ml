(*
 * Primitiva interactiveatization of implication.
 *)

include Czf_itt_and

open Printf
open Nl_debug

open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Conversionals
open Sequent
open Var

open Itt_logic
open Itt_rfun

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_implies%t" eflush

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Implication is restricted.
 *)
interactive fun_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "fun"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive fun_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "fun"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive implies_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "implies"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive implies_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "implies"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive iff_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "iff"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive iff_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "iff"{'A['x]; 'B['x]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Restricted.
 *)
let d_fun_funT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         fun_fun (hyp_count p) z p
   else
      raise (RefineError ("d_fun_funT", StringError "no elimination fimpliesm"))

let fun_fun_term = << fun_prop{z. "fun"{'P1['z]; 'P2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (fun_fun_term, d_fun_funT)

(*
 * Restricted.
 *)
let d_fun_resT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         fun_res (hyp_count p) z p
   else
      raise (RefineError ("d_fun_resT", StringError "no elimination fimpliesm"))

let fun_res_term = << restricted{z. "fun"{'P1['z]; 'P2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (fun_res_term, d_fun_resT)

(*
 * Restricted.
 *)
let d_implies_funT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         implies_fun (hyp_count p) z p
   else
      raise (RefineError ("d_implies_funT", StringError "no elimination fimpliesm"))

let implies_fun_term = << fun_prop{z. "implies"{'P1['z]; 'P2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (implies_fun_term, d_implies_funT)

(*
 * Restricted.
 *)
let d_implies_resT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         implies_res (hyp_count p) z p
   else
      raise (RefineError ("d_implies_resT", StringError "no elimination fimpliesm"))

let implies_res_term = << restricted{z. "implies"{'P1['z]; 'P2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (implies_res_term, d_implies_resT)

(*
 * Restricted.
 *)
let d_iff_funT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         iff_fun (hyp_count p) z p
   else
      raise (RefineError ("d_iff_funT", StringError "no elimination fiffm"))

let iff_fun_term = << fun_prop{z. "iff"{'P1['z]; 'P2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (iff_fun_term, d_iff_funT)

(*
 * Restricted.
 *)
let d_iff_resT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         iff_res (hyp_count p) z p
   else
      raise (RefineError ("d_iff_resT", StringError "no elimination fiffm"))

let iff_res_term = << restricted{z. "iff"{'P1['z]; 'P2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (iff_res_term, d_iff_resT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
