(*
 * These are the basic rewriting operations.
 *
 * We execute the operations outside the refiner.
 * After the refinement is done, we construct the
 * rewrite tree.
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

include Nltop

open Nl_debug
open Printf

open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError

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

(************************************************************************
 * INHERITANCE                                                          *
 ************************************************************************)

type env = Rewrite_type.env
type conv = Rewrite_type.conv

let env_term = Rewrite_type.env_term
let env_goal = Rewrite_type.env_goal

let rw = Rewrite_type.rw
let prefix_andthenC = Rewrite_type.prefix_andthenC
let prefix_orelseC = Rewrite_type.prefix_orelseC
let addrC = Rewrite_type.addrC
let idC = Rewrite_type.idC
let foldC = Rewrite_type.foldC
let makeFoldC = Rewrite_type.makeFoldC
let cutC = Rewrite_type.cutC
let funC = Rewrite_type.funC

(************************************************************************
 * SEARCH                                                               *
 ************************************************************************)

(*
 * Failure.
 *)
let failC err =
   funC (fun _ -> raise (RefineError ("failC", StringError err)))

let failWithC (name, err) =
   funC (fun _ -> raise (RefineError (name, err)))

(*
 * Trial.
 *)
let tryC rw =
   rw orelseC idC

(*
 * First subterm that works.
 *)
let someSubC conv =
   let someSubCE env =
      let t = env_term env in
      let count = subterm_count t in
      let rec subC i =
         if i = count then
            failWithC ("subC", StringError "all subterms failed")
         else
            (addrC [i] conv) orelseC (subC (i + 1))
      in
         subC 0
   in
      funC someSubCE

(*
 * Apply to all subterms.
 *)
let allSubC conv =
   let allSubCE conv env =
      let t = env_term env in
      let count = subterm_count t in
      let rec subC conv count i =
         if i = count then
            idC
         else
            (addrC [i] conv) andthenC (subC conv count (i + 1))
      in
         subC conv count 0
   in
      funC (allSubCE conv)

(*
 * Outermost terms.
 * HigherC has been moved into the refiner
 * for efficiency.
 *)
let higherC = Rewrite_type.higherC

let rwh conv i =
   rw (higherC conv) i

(*
 * Apply to leftmost-innermost term.
 *)
let rec lowerC rw =
   let lowerCE e =
      ((someSubC (lowerC rw)) orelseC rw)
   in
      funC lowerCE

(*
 * Apply to all terms possible from innermost to outermost.
 *)
let rec sweepUpC rw =
   let sweepUpCE e =
      ((allSubC (sweepUpC rw)) andthenC (tryC rw))
   in
      funC sweepUpCE

let rec sweepDnC rw =
   let sweepDnCE e =
      ((tryC rw) andthenC (allSubC (sweepDnC rw)))
   in
      funC sweepDnCE

(*
 * Use the first conversion that works.
 *)
let rec firstC = function
   [conv] ->
      conv
 | conv :: t ->
      conv orelseC firstC t
 | [] ->
      raise (RefineError ("firstC", StringError "empty argument list"))

(*
 * Repeat the conversion until nothing more happens.
 *)
let repeatC conv =
   let repeatCE env =
      let rec repeat t env =
         let t' = env_term env in
            (if alpha_equal t t' then
                idC
             else
                conv andthenC tryC (funC (repeat t')))
      in
      let t = env_term env in
         (conv andthenC (funC (repeat t)))
   in
      funC repeatCE

let rec repeatForC i conv =
   let repeatForCE env =
      if i = 0 then
         idC
      else
         conv andthenC (repeatForC (i - 1) conv)
   in
      funC repeatForCE

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
