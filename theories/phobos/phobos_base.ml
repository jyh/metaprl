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
extends Shell
extends Summary
extends Base_meta

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError

(*
 * New terms.
 *)
declare "true"
declare "false"

declare eq[a:n, b:n]{'t; 'f}
declare eq[a:s, b:s]{'t; 'f}
declare eq[a:v, b:v]{'t; 'f}
declare eq[a:t, b:t]{'t; 'f}
declare eq[a:l, b:l]{'t; 'f}

declare lt[a:n, b:n]{'t; 'f}
declare lt[a:s, b:s]{'t; 'f}
declare lt[a:t, b:t]{'t; 'f}
declare lt[a:l, b:l]{'t; 'f}

declare le[a:n, b:n]{'t; 'f}
declare le[a:s, b:s]{'t; 'f}
declare le[a:t, b:t]{'t; 'f}
declare le[a:l, b:l]{'t; 'f}

declare gt[a:n, b:n]{'t; 'f}
declare gt[a:s, b:s]{'t; 'f}
declare gt[a:t, b:t]{'t; 'f}
declare gt[a:l, b:l]{'t; 'f}

declare ge[a:n, b:n]{'t; 'f}
declare ge[a:s, b:s]{'t; 'f}
declare ge[a:t, b:t]{'t; 'f}
declare ge[a:l, b:l]{'t; 'f}

(*
 * Basic Phobos error terms.
 *)
declare error[msg:s]

(*
 * Parameter operations.
 *)
declare param_add_string[s:s]{'term}

(*
 * Utilities.
 *)
let error fn s term =
   raise (RefineError ("Phobos_base." ^ fn, StringTermError (s, term)))

(*
 * Error term raises exception.
 * If it has other than one string parameter, it is not touched.
 *)
let raise_error goal =
   let term = dest_term goal in
   let { term_op = operator; term_terms = subterms } = term in
   let { op_name = opname; op_params = params } = dest_op operator in
   match params with
      [s1] ->
         (match dest_param s1 with
            String msg ->
               raise (Invalid_argument ("Phobos: " ^ msg))
          | _ ->
               goal)
    | _ ->
         goal

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

ml_rw reduce_error0 : ('goal: error[msg:s]) =
   raise_error goal

prim_rw reduce_eq_num : eq[a:n, b:n]{'t; 'f} <--> meta_eq[a:n, b:n]{'t; 'f}
prim_rw reduce_eq_str : eq[a:s, b:s]{'t; 'f} <--> meta_eq[a:s, b:s]{'t; 'f}
prim_rw reduce_eq_var : eq[a:v, b:v]{'t; 'f} <--> meta_eq[a:v, b:v]{'t; 'f}
prim_rw reduce_eq_tok : eq[a:t, b:t]{'t; 'f} <--> meta_eq[a:t, b:t]{'t; 'f}
prim_rw reduce_eq_lev : eq[a:l, b:l]{'t; 'f} <--> meta_eq[a:l, b:l]{'t; 'f}

prim_rw reduce_lt_num : lt[a:n, b:n]{'t; 'f} <--> meta_lt[a:n, b:n]{'t; 'f}
prim_rw reduce_lt_str : lt[a:s, b:s]{'t; 'f} <--> meta_lt[a:s, b:s]{'t; 'f}
prim_rw reduce_lt_tok : lt[a:t, b:t]{'t; 'f} <--> meta_lt[a:t, b:t]{'t; 'f}
prim_rw reduce_lt_lev : lt[a:l, b:l]{'t; 'f} <--> meta_lt[a:l, b:l]{'t; 'f}

prim_rw reduce_le_num : le[a:n, b:n]{'t; 'f} <--> meta_lt[b:n, a:n]{'f; 't}
prim_rw reduce_le_str : le[a:s, b:s]{'t; 'f} <--> meta_lt[b:s, a:s]{'f; 't}
prim_rw reduce_le_tok : le[a:t, b:t]{'t; 'f} <--> meta_lt[b:t, a:t]{'f; 't}
prim_rw reduce_le_lev : le[a:l, b:l]{'t; 'f} <--> meta_lt[b:l, a:l]{'f; 't}

prim_rw reduce_gt_num : gt[a:n, b:n]{'t; 'f} <--> meta_lt[b:n, a:n]{'t; 'f}
prim_rw reduce_gt_str : gt[a:s, b:s]{'t; 'f} <--> meta_lt[b:s, a:s]{'t; 'f}
prim_rw reduce_gt_tok : gt[a:t, b:t]{'t; 'f} <--> meta_lt[b:t, a:t]{'t; 'f}
prim_rw reduce_gt_lev : gt[a:l, b:l]{'t; 'f} <--> meta_lt[b:l, a:l]{'t; 'f}

prim_rw reduce_ge_num : ge[a:n, b:n]{'t; 'f} <--> meta_lt[a:n, b:n]{'f; 't}
prim_rw reduce_ge_str : ge[a:s, b:s]{'t; 'f} <--> meta_lt[a:s, b:s]{'f; 't}
prim_rw reduce_ge_tok : ge[a:t, b:t]{'t; 'f} <--> meta_lt[a:t, b:t]{'f; 't}
prim_rw reduce_ge_lev : ge[a:l, b:l]{'t; 'f} <--> meta_lt[a:l, b:l]{'f; 't}

(*
 * -*-
 * Local Variables:
 * Caml-master: "mp.run"
 * End:
 * -*-
 *)
