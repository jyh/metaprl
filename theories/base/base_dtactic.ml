(*
 * The D tactic performs a case selection on the conclusion opname.
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

include Base_auto_tactic

open Printf
open Mp_debug

open Opname
open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print
open Term_table

open Tacticals
open Sequent

open Base_auto_tactic
open Mptop

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Base_dtactic%t" eflush

let debug_dtactic =
   create_debug (**)
      { debug_name = "dtactic";
        debug_description = "display dT tactic operations";
        debug_value = false
      }

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * The d_tactic uses a term_table to match against terms.
 *)
type d_data = (int -> tactic) term_table

resource (term * (int -> tactic), int -> tactic, d_data, meta_term * tactic) d_resource

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Extract a D tactic from the data.
 * The tactic checks for an optable.
 *)
let extract_data tbl =
   let d i p =
      let t =
         (* Get the term described by the number *)
         if i = 0 then
            concl p
         else
            snd (nth_hyp p i)
      in
      let tac =
         try
            (* Find and apply the right tactic *)
            if !debug_dtactic then
               eprintf "Base_dtactic: lookup %s%t" (SimplePrint.string_of_opname (opname_of_term t)) eflush;
            let _, _, tac = Term_table.lookup "Base_dtactic.extract_data" tbl t in
               tac
         with
            Not_found ->
               raise (RefineError ("extract_data", StringTermError ("D tactic doesn't know about", t)))
      in
         if !debug_dtactic then
            eprintf "Base_dtactic: applying %s%t" (SimplePrint.string_of_opname (opname_of_term t)) eflush;
         tac i p
   in
      d

(*
 * Add a new tactic.
 *)
let improve_data (t, tac) tbl =
   Refine_exn.print Dform.null_base (insert tbl t) tac

(*
 * Wrap up the joiner.
 *)
let join_resource = join_tables

let extract_resource = extract_data

let improve_resource data x =
   if !debug_dtactic then
      begin
         let t, _ = x in
         let opname = opname_of_term t in
            eprintf "Base_dtactic.improve_resource: %s%t" (string_of_opname opname) eflush
      end;
   improve_data x data

let close_resource rsrc modname =
   rsrc

(*
 * Resource.
 *)
let d_resource =
   Mp_resource.create (**)
      { resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource;
        resource_improve_arg = Mp_resource.improve_arg_fail "d_resource";
        resource_close = close_resource
      }
      (new_table ())

let get_resource modname =
   Mp_resource.find d_resource modname

let rec add_d_info rr = function
   (t, tac) :: tl ->
      add_d_info (Mp_resource.improve rr (t, tac)) tl
 | [] ->
      rr

let dT i p =
   Sequent.get_int_tactic_arg p "d" i p

let rec dForT i =
   if i <= 0 then
      idT
   else
      dT 0 thenMT dForT (i - 1)

(*
 * By default, dT 0 should always make progress.
 *)
let d_prec = create_auto_prec [trivial_prec] []

let auto_resource =
   Mp_resource.improve auto_resource (**)
      { auto_name = "dT";
        auto_prec = d_prec;
        auto_tac = auto_wrap (dT 0)
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
