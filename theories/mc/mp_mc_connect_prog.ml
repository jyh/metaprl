(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Operations for converting between MCC Fir expressions and MetaPRL terms.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
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
 * Author: Brian Emre Aydemir
 * Email:  emre@its.caltech.edu
 *)

(* Open MCC ML namespaces. *)

open Rawint
open Rawfloat
open Fir

(* Open MetaPRL ML namespaces. *)

open Refiner.Refiner.RefineError
open Itt_rfun
open Mp_mc_fir_prog
open Mp_mc_connect_base
open Mp_mc_connect_ty
open Mp_mc_connect_exp

(*
 * Convert to and from fundef.
 *)

(* Define helper functions for creating / destructing the function body. *)

let rec term_of_body vars exp =
   match vars with
      [] ->
         raise (Invalid_argument "term_of_body: function with no args!")
    | [a] ->
         mk_lambda_term    (string_of_var a)
                           (term_of_exp exp)
    | h :: t ->
         mk_lambda_term    (string_of_var h)
                           (term_of_body t exp)

let rec body_of_term arg_list term =
   if is_lambda_term term then
      let arg, body = dest_lambda term in
         body_of_term ((var_of_string arg) :: arg_list) body
   else
      List.rev arg_list, exp_of_term term

(* Define the actual conversion functions now. *)

let term_of_fundef (line, ty, vars, exp) =
   mk_fundef_term    (term_of_debug_line line)
                     (term_of_ty ty)
                     (term_of_body vars exp)

let fundef_of_term t =
   try
      let line, ty, body = dest_fundef_term t in
      let vars, exp = body_of_term [] body in
         (debug_line_of_term line),
         (ty_of_term ty),
         vars,
         exp
   with
      (* Reprint errors to narrow down term with error. *)
      _ -> report_error "fundef_of_term" t
