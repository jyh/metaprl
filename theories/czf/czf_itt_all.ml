(*
 * Primitiva interactiveatization of implication.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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
open Nl_debug

open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Nl_resource

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

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_and%t" eflush

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Implication is restricted.
 *)
interactive dfun_fun3 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'A['z]} } -->
   sequent ['ext] { 'H >- dfun_prop{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- fun_prop{z. "fun"{'A['z]; w. 'B['z; 'w]}} }

interactive dfun_res3 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- restricted{z. "fun"{'A['z]; w. 'B['z; 'w]}} }

interactive all_fun 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'A['z]} } -->
   sequent ['ext] { 'H >- dfun_prop{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- fun_prop{z. "all"{'A['z]; w. 'B['z; 'w]}} }

interactive all_res 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- restricted{z. "all"{'A['z]; w. 'B['z; 'w]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Also decompose iffs in the hyps.
 *)
let d_iffT i p =
   let _, hyp = Sequent.nth_hyp p i in
      if is_iff_term hyp then
         dT i p
      else
         raise (RefineError ("d_iffT", StringError "not an iff"))

(*
 * Our auto tactic needs to chain trhough aplications and fst.
 *)
let allAutoT =
   repeatT (firstT [progressT autoT;
                    autoApplyT 0;
                    progressT (rwh (reduceFst orelseC reduceSnd) 0);
                    onSomeHypT d_iffT;
                    idT])

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
let d_dfun_funT i p =
   if i = 0 then
      let u, v, z = maybe_new_vars3 p "u" "v" "z" in
         (dfun_fun3 (hyp_count_addr p) u v z thenLT labels) p
   else
      raise (RefineError ("d_dfun_funT", StringError "no elimination fandm"))

let dfun_fun_term = << fun_prop{z. "fun"{'P1['z]; w. 'P2['z; 'w]}} >>

let d_resource = d_resource.resource_improve d_resource (dfun_fun_term, d_dfun_funT)

(*
 * Restricted.
 *)
let d_dfun_resT i p =
   if i = 0 then
      let u, v, z = maybe_new_vars3 p "u" "v" "z" in
         (dfun_res3 (hyp_count_addr p) u v z thenLT labels) p
   else
      raise (RefineError ("d_dfun_resT", StringError "no elimination fandm"))

let dfun_res_term = << restricted{z. "fun"{'P1['z]; w. 'P2['z; 'w]}} >>

let d_resource = d_resource.resource_improve d_resource (dfun_res_term, d_dfun_resT)

(*
 * Functionality.
 *)
let d_all_funT i p =
   if i = 0 then
      let u, v, z = maybe_new_vars3 p "u" "v" "z" in
         (all_fun (hyp_count_addr p) u v z thenLT labels) p
   else
      raise (RefineError ("d_all_funT", StringError "no elimination fandm"))

let all_fun_term = << fun_prop{z. "all"{'P1['z]; w. 'P2['z; 'w]}} >>

let d_resource = d_resource.resource_improve d_resource (all_fun_term, d_all_funT)

(*
 * Restricted.
 *)
let d_all_resT i p =
   if i = 0 then
      let u, v, z = maybe_new_vars3 p "u" "v" "z" in
         (all_res (hyp_count_addr p) u v z thenLT labels) p
   else
      raise (RefineError ("d_all_resT", StringError "no elimination fandm"))

let all_res_term = << restricted{z. "all"{'P1['z]; w. 'P2['z; 'w]}} >>

let d_resource = d_resource.resource_improve d_resource (all_res_term, d_all_resT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
