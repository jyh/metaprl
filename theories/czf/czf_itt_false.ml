(*
 * Logical false.
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

