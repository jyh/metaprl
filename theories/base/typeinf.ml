(*
 * Before anything, we start the type inference resource.
 * This is mostly an incomplete type inference algorithm, but
 * it is used to perform basic inference.
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

open Printf
open Mp_debug

open Refiner.Refiner
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermAddr
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Term_match_table
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Typeinf%t" eflush

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * This resource is used to analyze the sequent to gather type info.
 * The subst_fun gets a clause from the current sequent or its
 * assumptions.
 *)
type typeinf_subst_fun = term_subst -> (string option * term) -> term_subst
type typeinf_subst_info = term * typeinf_subst_fun
type typeinf_subst_data = (typeinf_subst_fun, typeinf_subst_fun) term_table

resource (typeinf_subst_info, typeinf_subst_fun, typeinf_subst_data, unit) typeinf_subst_resource

(*
 * This is the type of the inference algorithm.
 *)
type typeinf_func = unify_subst -> term -> unify_subst * term

(*
 * Modular components also get a recursive instance of
 * the inference algorithm.
 *)
type typeinf_comp = typeinf_func -> typeinf_func

(*
 * This is the resource addition.
 *)
type typeinf_resource_info = term * typeinf_comp

(*
 * Internal type.
 *)
type typeinf_data = (typeinf_comp, typeinf_comp) term_table

(*
 * The resource itself.
 *)
resource (typeinf_resource_info, typeinf_func, typeinf_data, unit) typeinf_resource

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Infer the type of a term from the table.
 *)
let identity x = x

let collect (tbl : (typeinf_subst_fun, typeinf_subst_fun) term_table) subst (so, t) =
   let inf =
      try snd (lookup "Typeinf.collect" tbl identity t) with
         Not_found ->
            raise (RefineError ("Typeinf.collect", StringTermError ("can't collect type for", t)))
   in
      inf subst (so, t)

(*
 * Wrap up the algorithm.
 *)
let join_subst_resource = join_tables

let extract_subst_resource = collect

let improve_subst_resource tbl (t, inf) =
   insert tbl t inf

let close_subst_resource rsrc modname =
   rsrc

(*
 * Resource.
 *)
let typeinf_subst_resource =
   Mp_resource.create (**)
      { resource_join = join_subst_resource;
        resource_extract = extract_subst_resource;
        resource_improve = improve_subst_resource;
        resource_improve_arg = Mp_resource.improve_arg_fail "typeinf_subst_resource";
        resource_close = close_subst_resource
      }
      (new_table ())

let get_typeinf_subst_resource modname =
   Mp_resource.find typeinf_subst_resource modname

(*
 * Projector.
 *)
let collect_subst p =
   let collect = get_tsubst_arg p "typeinf_subst" in
   let rec filter_hyps subst hyps i len =
      if i = len then
         subst
      else
         match SeqHyp.get hyps i with
            Hypothesis (v, t) ->
               let subst = (v, t) :: subst in
               let subst =
                  try collect subst (Some v, t) with
                     RefineError _ ->
                        subst
               in
                  filter_hyps subst hyps (i + 1) len
          | _ ->
               filter_hyps subst hyps (i + 1) len
   in
   let goal, assums = dest_msequent (Sequent.msequent p) in
   let { sequent_hyps = hyps } = TermMan.explode_sequent goal in
   let num_hyps = TermMan.num_hyps goal in
   let rec filter_assums subst = function
      assum :: tl ->
         let num_hyps' = TermMan.num_hyps assum in
            if num_hyps' <= num_hyps then
               let concl = TermMan.nth_concl assum 1 in
               let subst =
                  try collect subst (None, concl) with
                     RefineError _ ->
                        subst
               in
                  filter_assums subst tl
            else
               subst
    | [] ->
         subst
   in
   let subst = filter_hyps [] hyps 0 (SeqHyp.length hyps) in
      filter_assums subst assums

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Infer the type of a term from the table.
 *)
let infer tbl =
   let rec aux decl t =
      if is_var_term t then
         let v = dest_var t in
            try decl, List.assoc v (subst_of_unify_subst decl) with
               Not_found ->
                  raise (RefineError ("typeinf", StringTermError ("can't infer type for", t)))
      else
         let inf =
            try snd (lookup "Typeinf.infer" tbl identity t) with
               Not_found ->
                  raise (RefineError ("typeinf", StringTermError ("can't infer type for", t)))
         in
            inf aux decl t
   in
      aux

(*
 * Wrap up the algorithm.
 *)
let join_resource = join_tables

let extract_resource = infer

let improve_resource tbl (t, inf) =
   insert tbl t inf

let close_resource rsrc modname =
   rsrc

(*
 * Resource.
 *)
let typeinf_resource =
   Mp_resource.create (**)
      {  resource_join = join_resource;
         resource_extract = extract_resource;
         resource_improve = improve_resource;
         resource_improve_arg = Mp_resource.improve_arg_fail "typeinf_resource";
         resource_close = close_resource
      }
      (new_table ())

let get_typeinf_resource modname =
   Mp_resource.find typeinf_resource modname

(*
 * Projector.
 *)
let typeinf_of_proof p =
   get_typeinf_arg p "typeinf"

let infer_type p t =
   let subst = collect_subst p in
      (get_typeinf_arg p "typeinf") (unify_subst_of_subst subst) t

let infer_type_args p t =
   let t =
      try get_with_arg p with
         RefineError _ ->
            snd (infer_type p t)
   in
      [t]

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
