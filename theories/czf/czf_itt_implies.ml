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

include Czf_itt_and

open Printf
open Mp_debug

open Refiner.Refiner.RefineError
open Mp_resource

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
         fun_fun (hyp_count_addr p) z p
   else
      raise (RefineError ("d_fun_funT", StringError "no elimination fimpliesm"))

let fun_fun_term = << fun_prop{z. "fun"{'P1['z]; 'P2['z]}} >>

let d_resource = Mp_resource.improve d_resource (fun_fun_term, d_fun_funT)

(*
 * Restricted.
 *)
let d_fun_resT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         fun_res (hyp_count_addr p) z p
   else
      raise (RefineError ("d_fun_resT", StringError "no elimination fimpliesm"))

let fun_res_term = << restricted{z. "fun"{'P1['z]; 'P2['z]}} >>

let d_resource = Mp_resource.improve d_resource (fun_res_term, d_fun_resT)

(*
 * Restricted.
 *)
let d_implies_funT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         implies_fun (hyp_count_addr p) z p
   else
      raise (RefineError ("d_implies_funT", StringError "no elimination fimpliesm"))

let implies_fun_term = << fun_prop{z. "implies"{'P1['z]; 'P2['z]}} >>

let d_resource = Mp_resource.improve d_resource (implies_fun_term, d_implies_funT)

(*
 * Restricted.
 *)
let d_implies_resT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         implies_res (hyp_count_addr p) z p
   else
      raise (RefineError ("d_implies_resT", StringError "no elimination fimpliesm"))

let implies_res_term = << restricted{z. "implies"{'P1['z]; 'P2['z]}} >>

let d_resource = Mp_resource.improve d_resource (implies_res_term, d_implies_resT)

(*
 * Restricted.
 *)
let d_iff_funT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         iff_fun (hyp_count_addr p) z p
   else
      raise (RefineError ("d_iff_funT", StringError "no elimination fiffm"))

let iff_fun_term = << fun_prop{z. "iff"{'P1['z]; 'P2['z]}} >>

let d_resource = Mp_resource.improve d_resource (iff_fun_term, d_iff_funT)

(*
 * Restricted.
 *)
let d_iff_resT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         iff_res (hyp_count_addr p) z p
   else
      raise (RefineError ("d_iff_resT", StringError "no elimination fiffm"))

let iff_res_term = << restricted{z. "iff"{'P1['z]; 'P2['z]}} >>

let d_resource = Mp_resource.improve d_resource (iff_res_term, d_iff_resT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
