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

open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent
open Var

open Itt_logic
open Itt_rfun

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_and%t" eflush

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Implication is restricted.
 *)
interactive prod_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "prod"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive prod_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "prod"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive and_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "and"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive and_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "and"{'A['x]; 'B['x]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Restricted.
 *)
let d_prod_funT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         prod_fun (hyp_count_addr p) z p
   else
      raise (RefineError ("d_prod_funT", StringError "no elimination fandm"))

let prod_fun_term = << fun_prop{z. "prod"{'P1['z]; 'P2['z]}} >>

let d_resource = Mp_resource.improve d_resource (prod_fun_term, d_prod_funT)

(*
 * Restricted.
 *)
let d_prod_resT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         prod_res (hyp_count_addr p) z p
   else
      raise (RefineError ("d_prod_resT", StringError "no elimination fandm"))

let prod_res_term = << restricted{z. "prod"{'P1['z]; 'P2['z]}} >>

let d_resource = Mp_resource.improve d_resource (prod_res_term, d_prod_resT)

(*
 * Restricted.
 *)
let d_and_funT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         and_fun (hyp_count_addr p) z p
   else
      raise (RefineError ("d_and_funT", StringError "no elimination fandm"))

let and_fun_term = << fun_prop{z. "and"{'P1['z]; 'P2['z]}} >>

let d_resource = Mp_resource.improve d_resource (and_fun_term, d_and_funT)

(*
 * Restricted.
 *)
let d_and_resT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         and_res (hyp_count_addr p) z p
   else
      raise (RefineError ("d_and_resT", StringError "no elimination fandm"))

let and_res_term = << restricted{z. "and"{'P1['z]; 'P2['z]}} >>

let d_resource = Mp_resource.improve d_resource (and_res_term, d_and_resT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
