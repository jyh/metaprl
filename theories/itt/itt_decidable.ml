(*!
 * @spelling{decideT}
 *
 * @begin[doc]
 * @theory[Itt_decidable]
 *
 * It is occasionally useful to assert the @emph{decidability}
 * of a proposition $P$.  The proposition is decidable if
 * $P @vee @not{P}$.  Decidable propositions allow reasoning
 * by case analysis.
 *
 * The @tt{Itt_decidable} module defines a generic resource,
 * and a tactic @hreftactic[decideT] to help prove the decidability
 * of propositions.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * Author: Aleksey Nogin
 * @email{nogin@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Itt_logic
(*! @docoff *)

open Printf
open Mp_debug
open Mp_resource
open Term_match_table
open Tactic_type
open Tactic_type.Tacticals
open Base_auto_tactic

open Refiner.Refiner
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMeta
open Refiner.Refiner.RefineError

let _ =
   show_loading "Loading Itt_decidable%t"

(************************************************************************
 * decidable                                                            *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The definition of $@decidable{P}$ if $@or{P; @not{P}}$.
 * @end[doc]
 *)
define unfold_decidable : decidable{'p} <--> ( 'p or not {'p} )
(*! @docoff *)

dform decidable_df : except_mode[src] :: decidable{'p} = `"Decidable(" 'p `")"

interactive_rw fold_decidable : ( 'p or not {'p} ) <--> decidable{'p}

(*!
 * @begin[doc]
 * @rules
 *
 * The @tt{assert_decidable} rule allows case analysis
 * over a decidable proposition $p$.
 * @end[doc]
 *)
interactive assert_decidable 'H 'p :
   [decidable] sequent ['ext]  { 'H >- decidable {'p} } -->
   sequent ['ext] { 'H; x: 'p >- 'G } -->
   sequent ['ext] { 'H; x: not{'p} >- 'G } -->
   sequent ['ext] { 'H >- 'G }

let decidable_term = <<decidable{'p}>>
let decidable_opname = opname_of_term decidable_term
let is_decidable_term = is_dep0_term decidable_opname
let mk_decidable_term = mk_dep0_term decidable_opname

let dest_decidable_term term =
   try
      dest_dep0_term decidable_opname term
   with RefineError _ ->
      raise (RefineError ("Itt_decidable.dest_decidable_term", TermError term))

(************************************************************************
 * decide_resource                                                      *
 ************************************************************************)

type decide_data = (term * tactic) list

(*!
 * @begin[doc]
 * @resources
 *
 * The @tt{decide_resource} provides a resource for reasoning about
 * decidability of propositions.  The argument @code{term * tactic}
 * provides a term that matches the goal to be proved, and a tactic
 * to prove goals of that form.
 * @end[doc]
 *)
(*! @docoff *)

let identity x = x

let ref_exn =
   RefineError("Itt_decidable.extract_data", StringError "no applicable rule found")

let extract_data tbl p =
   let t = dest_decidable_term (Sequent.concl p) in
   try
      (snd (Term_match_table.lookup tbl t)) p
   with Not_found -> raise ref_exn

let process_decide_resource_annotation name context_args var_args term_args _ statement pre_tactic =
   let _, goal = unzip_mfunction statement in
   let t =
      try TermMan.nth_concl goal 1 with
         RefineError _ ->
            raise (Invalid_argument (sprintf "Itt_decidable.improve_arg: %s: must be an introduction rule" name))
   in
   let term_args =
      match term_args with
         [] ->
            (fun _ -> [])
       | _ ->
            let length = List.length term_args in
               (fun p ->
                     let args =
                        try get_with_args p with
                           RefineError _ ->
                              raise (RefineError (name, StringIntError ("arguments required", length)))
                     in
                     let length' = List.length args in
                        if length' != length then
                           raise (RefineError (name, StringIntError ("wrong number of arguments", length')));
                        args)
   in
   let tac =
      match context_args with
         [|_|] ->
            (fun p ->
                  let vars = Var.maybe_new_vars_array p var_args in
                  let addr = Sequent.hyp_count_addr p in
                     Tactic_type.Tactic.tactic_of_rule pre_tactic ([| addr |], vars) (term_args p) p)
       | _ ->
            raise (Invalid_argument (sprintf "Itt_decidable.improve_arg: %s: not an introduction rule" name))
   in
      (t,tac)

let resource decide =
   table_resource_info identity extract_data

let step_decidableT p = Sequent.get_resource_arg p get_decide_resource p

let step_decidable_or_autoT p =
   let tac =
      if is_decidable_term (Sequent.concl p) then
         step_decidableT else autoT
   in
      tac p

let decidable_or_autoT = repeatT step_decidable_or_autoT

let prove_decidableT = step_decidableT thenT decidable_or_autoT

(*!
 * @begin[doc]
 * @tactics
 *
 * The @tactic[decideT] tactic applies the @hrefrule[assert_decidable]
 * on a specific proposition $P$.
 *
 * $$
 * @rulebox{decideT; P;
 *   @sequent{squash; H; @decidable{P}}@cr
 *     @sequent{ext; {H; x@colon P}; C}@cr
 *     @sequent{ext; {H; x@colon @not{P}}; C};
 *   @sequent{ext; H; C}}
 * $$
 *
 * @docoff
 * @end[doc]
 *)
let decideT t p =
   let tac =
      assert_decidable (Sequent.hyp_count_addr p) t
      thenLT [tryT (completeT prove_decidableT); idT; idT]
   in
      tac p

(*!
 * @begin[doc]
 * @thysubsection{Basic decidability}
 *
 * The propositions $@true$ and $@false$ are always decidable.
 * @end[doc]
 *)
interactive dec_false {| decide |} 'H :
   sequent ['ext] { 'H >- decidable{."false"} }

interactive dec_true {| decide |} 'H :
   sequent ['ext] { 'H >- decidable{."true"} }
(*! @docoff *)
