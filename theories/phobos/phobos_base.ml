(*
 * Miscellaneous rewrites for Phobos.
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
 * Copyright (C) 2002 Adam Granicz, Caltech
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
 * Author: Adam Granicz <granicz@cs.caltech.edu>
 *
 *)
extends Mptop
extends Summary

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError

(*
 * Parameter operations.
 *)
declare param_add_string[s:s]{'term}

let error fn s term =
   raise (RefineError ("Phobos_base." ^ fn, StringTermError (s, term)))

(*
 * String parameter addition.
 *)
let ml_param_add_string goal =
   let term = dest_term goal in
   let { term_op = operator; term_terms = subterms } = term in
   let { op_name = opname; op_params = params } = dest_op operator in
   match params with
      [s1] ->
         (match dest_param s1 with
               String s1 ->
                  if List.length subterms = 1 then begin
                     let { bvars = bound_vars; bterm = term } = dest_bterm (List.hd subterms) in
                     let { term_op = operator; term_terms = subterms } = dest_term term in
                     let { op_name = opname; op_params = params } = dest_op operator in
                     (match params with
                        [s2] ->
                           (match dest_param s2 with
                              String s2 ->
                                 mk_term (mk_op opname [make_param (String (s2 ^ s1))]) subterms
                            | _ ->
                                 error "param_add_string" "subterm parameter type mismatch" goal
                           )
                      | _ ->
                           error "param_add_string" "subterm doesn't have one string parameter" goal
                     )
                  end else
                     error "param_add_string" "subterm arity mismatch (<>1)" goal
             | _ ->
                  error "param_add_string" "parameter type mismatch" goal
         )
    | _ ->
         error "param_add_string" "ill-formed operation" goal

(*
 * param_add_string[add:s]{term[param:s]{..subterms..}} -> term[param+add:s]{..subterms..}
 *)
ml_rw reduce_param_add_string : ('goal : param_add_string[s:s]{'term}) =
   ml_param_add_string goal

(*
 * -*-
 * Local Variables:
 * Caml-master: "mp.run"
 * End:
 * -*-
 *)
