(*
 * Primitiva interactiveatization of implication.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 * 
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

include Czf_itt_sep

open Printf
open Mp_debug

open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Mp_resource

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
         (dprod_fun3 (hyp_count_addr p) u v z thenLT labels) p
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
         (dprod_res3 (hyp_count_addr p) u v z thenLT labels) p
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
         (exists_fun (hyp_count_addr p) u v z thenLT labels) p
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
         (exists_res (hyp_count_addr p) u v z thenLT labels) p
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
