(*
 * These are the basic rewriting operations.
 *
 * We execute the operations outside the refiner.
 * After the refinement is done, we construct the
 * rewrite tree.
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

include Mptop

open Mp_debug
open Printf

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError

open Mp_resource
open Simple_print
open Term_match_table

open Tactic_type.Conversionals

(*
 * Debug statement.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Tacticals%t" eflush

let debug_conv =
   create_debug (**)
      { debug_name = "conv";
        debug_description = "display conversion operation";
        debug_value = false
      }

let debug_reduce =
   create_debug (**)
      { debug_name = "reduce";
        debug_description = "display reductions";
        debug_value = false
      }

(*
 * Toploop values.
 *)
let rw = Tactic_type.Conversionals.rw
let rwh = Tactic_type.Conversionals.rwh
let rwc = Tactic_type.Conversionals.rwc
let rwch = Tactic_type.Conversionals.rwch
let prefix_andthenC = Tactic_type.Conversionals.prefix_andthenC
let prefix_orelseC = Tactic_type.Conversionals.prefix_orelseC
let addrC = Tactic_type.Conversionals.addrC
let clauseC = Tactic_type.Conversionals.clauseC
let idC = Tactic_type.Conversionals.idC
let foldC = Tactic_type.Conversionals.foldC
let makeFoldC = Tactic_type.Conversionals.makeFoldC
let cutC = Tactic_type.Conversionals.cutC
let failC = Tactic_type.Conversionals.failC
let tryC = Tactic_type.Conversionals.tryC
let someSubC = Tactic_type.Conversionals.someSubC
let allSubC = Tactic_type.Conversionals.allSubC
let higherC = Tactic_type.Conversionals.higherC
let lowerC = Tactic_type.Conversionals.lowerC
let sweepUpC = Tactic_type.Conversionals.sweepUpC
let sweepDnC = Tactic_type.Conversionals.sweepDnC
let firstC = Tactic_type.Conversionals.firstC
let repeatC = Tactic_type.Conversionals.repeatC
let repeatForC = Tactic_type.Conversionals.repeatForC

(************************************************************************
 * REDUCTION RESOURCE                                                   *
 ************************************************************************)

type reduce_data = (conv, conv) term_table

resource (term * conv, conv, reduce_data, conv) reduce_resource

(*
 * Extract a D tactic from the data.
 * The tactic checks for an optable.
 *)
let identity x = x

let extract_data tbl =
   let rw e =
      let t = env_term e in
      let conv =
         try
            (* Find and apply the right tactic *)
            if !debug_reduce then
               eprintf "Conversionals: lookup %a%t" debug_print t eflush;
            snd (Term_match_table.lookup "Conversionals.extract_data" tbl identity t)
         with
            Not_found ->
               raise (RefineError ("Conversionals.extract_data", StringTermError ("no reduction for", t)))
      in
         if !debug_reduce then
            eprintf "Conversionals: applying %a%t" debug_print t eflush;
         conv
   in
      funC rw

(*
 * Add a new tactic.
 *)
let improve_data (t, conv) tbl =
   Refine_exn.print Dform.null_base (insert tbl t) conv

(*
 * Wrap up the joiner.
 *)
let join_resource base1 base2 =
   join_tables base1 base2

let extract_resource = extract_data

let improve_resource data x =
   if !debug_reduce then
      begin
         let t, _ = x in
         let opname = opname_of_term t in
            eprintf "Conversionals.improve_resource: %a%t" debug_print t eflush
      end;
   improve_data x data

let improve_resource_arg data name cvars vars args params mterm conv =
   match mterm with
      MetaIff (MetaTheorem t, _) ->
         improve_resource data (t, conv)
    | _ ->
         raise (RefineError ("Conversionals.improve_resource_arg", StringError "not a simple rewrite"))

let close_resource rsrc modname =
   rsrc

(*
 * Resource.
 *)
let reduce_resource =
   Mp_resource.create (**)
      { resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource;
        resource_improve_arg = improve_resource_arg;
        resource_close = close_resource
      }
      (new_table ())

let get_resource modname =
   Mp_resource.find reduce_resource modname

let rec add_reduce_info rr = function
   (t, conv) :: tl ->
      add_reduce_info (Mp_resource.improve rr (t, conv)) tl
 | [] ->
      rr

let reduceTopC_env e =
   get_conv (env_arg e) "reduce"

let reduceTopC = funC reduceTopC_env

let reduceC =
   repeatC (higherC reduceTopC)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
