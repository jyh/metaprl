(*
 * Logical true.
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

open Tactic_type.Sequent
open Mp_resource
open Tactic_type.Tacticals

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
      true_fun (hyp_count_addr p) p
   else
      raise (RefineError ("d_true_funT", StringError "no elimination form"))

let true_fun_term = << fun_prop{x. "true"} >>

let d_resource = Mp_resource.improve d_resource (true_fun_term, d_true_funT)

(*
 * Restricted.
 *)
let d_true_resT i p =
   if i = 0 then
      true_res (hyp_count_addr p) p
   else
      raise (RefineError ("d_true_resT", StringError "no elimination form"))

let true_res_term = << restricted{x. "true"} >>

let d_resource = Mp_resource.improve d_resource (true_res_term, d_true_resT)

(*
 * Restricted.
 *)
let d_unit_funT i p =
   if i = 0 then
      unit_fun (hyp_count_addr p) p
   else
      raise (RefineError ("d_unit_funT", StringError "no elimination form"))

let unit_fun_term = << fun_prop{x. "unit"} >>

let d_resource = Mp_resource.improve d_resource (unit_fun_term, d_unit_funT)

(*
 * Restricted.
 *)
let d_unit_resT i p =
   if i = 0 then
      unit_res (hyp_count_addr p) p
   else
      raise (RefineError ("d_unit_resT", StringError "no elimination form"))

let unit_res_term = << restricted{x. "unit"} >>

let d_resource = Mp_resource.improve d_resource (unit_res_term, d_unit_resT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
