(*
 * These are some extra derived rules to make proofs easier.
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

include Itt_fun
include Itt_prod
include Itt_struct
include Itt_logic

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Mptop
open Typeinf

open Tactic_type
open Tactic_type.Tacticals

open Itt_rfun
open Itt_logic
open Itt_struct
open Itt_equal

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * To prove an application,
 * Show that the function is family of types,
 * and the argument is an index.
 *)
interactive applyIntro 'H (x: 'A -> 'B['x]) (bind{y. 'C['y]}) 'f 'a :
   [wf] sequent [squash] { 'H >- 'a IN 'A } -->
   [wf] sequent [squash] { 'H >- 'f IN (x: 'A -> 'B['x]) } -->
   [wf] sequent [squash] { 'H >- "type"{'B['a]} } -->
   [wf] sequent [squash] { 'H; y: 'B['a] >- "type"{'C['y]} } -->
   [main] sequent ['ext] { 'H; y: 'B['a] >- 'C['y] } -->
   sequent ['ext] { 'H >- 'C['f 'a] }

(*
 * To prove an application,
 * Show that the function is family of types,
 * and the argument is an index.
 *)
interactive independentApplyIntro 'H ('A -> 'B) (bind{y. 'C['y]}) 'f 'a :
   [wf] sequent [squash] { 'H >- 'a IN 'A } -->
   [wf] sequent [squash] { 'H >- 'f IN ('A -> 'B) } -->
   [wf] sequent [squash] { 'H; y: 'B >- "type"{'C['y]} } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   [main] sequent ['ext] { 'H; y: 'B >- 'C['y] } -->
   sequent ['ext] { 'H >- 'C['f 'a] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Add them as resources.
 *)
let applyT app i p =
   if i = 0 then
      let f, a = dest_apply app in
      let goal_type =
         try get_with_arg p with
            RefineError _ ->
               infer_type p f
      in
      let goal_type, tac =
         if is_dfun_term goal_type then
            goal_type, applyIntro
         else if is_all_term goal_type then
            let v, a, b = dest_all goal_type in
               mk_dfun_term v a b, applyIntro
         else if is_fun_term goal_type then
            goal_type, independentApplyIntro
         else if is_implies_term goal_type then
            let a, b = dest_implies goal_type in
               mk_fun_term a b, independentApplyIntro
         else
            raise (RefineError ("d_applyT", StringTermError ("not a function type", goal_type)))
      in
      let v = maybe_new_vars1 p "v" in
      let bind = mk_bind_term v (var_subst (Sequent.concl p) app v) in
         tac (Sequent.hyp_count_addr p) goal_type bind f a p
   else
      raise (RefineError ("d_applyT", StringError "no elimination form"))

(*
 * Search for an application that we can reduce.
 * In this heuristic, we don't descend into the type in equalities.
 *)
let add_term app apps =
   let rec search app = function
      app' :: apps ->
         if alpha_equal app app' then
            true
         else
            search app apps
    | [] ->
         false
   in
      if search app apps then
         apps
      else
         app :: apps

let search_apply =
   let rec search apps vars goal =
      if is_apply_term goal then
         let f, a = dest_apply goal in
            if is_var_term f & List.mem (dest_var f) vars then
               search_term (add_term goal apps) vars goal
            else
               search_term apps vars goal
      else
         search_term apps vars goal
   and search_term apps vars goal =
      let { term_op = op; term_terms = bterms } = dest_term goal in
         if is_equal_term goal then
            search_bterms apps vars (List.tl bterms)
         else
            search_bterms apps vars bterms
   and search_bterms apps vars = function
      bterm :: bterms ->
         let apps = search apps vars (dest_bterm bterm).bterm in
            search_bterms apps vars bterms
    | [] ->
         apps
   in
      search []

(*
 * Search for a possible application in the conclusion.
 * This is quite heuristic.  We don't descend into
 * the types for equalities.
 *)
let rec anyApplyT apps i p =
   match apps with
      [app] ->
         applyT app i p
    | app :: apps ->
         (applyT app i orelseT anyApplyT apps i) p
    | [] ->
         raise (RefineError ("anyApplyT", StringError "no applications found"))

let autoApplyT i p =
   let goal = Sequent.concl p in
      if is_type_term goal then
         raise (RefineError ("autoApplyT", StringError "don't apply to 'type' goals"))
      else
         let vars = Sequent.declared_vars p in
         let apps =
            if i = 0 then
               search_apply vars (Sequent.concl p)
            else
               let _, hyp = Sequent.nth_hyp p i in
                  search_apply vars hyp
         in
            anyApplyT apps i p

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
