(*
 * These are some extra derived rules to make proofs easier.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
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
extends Itt_prod
extends Itt_struct
extends Itt_logic

open Term_sig
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError

open Var
open Typeinf
open Lm_symbol

open Tactic_type
open Tactic_type.Tacticals

open Itt_dfun
open Itt_logic
open Itt_equal

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * To prove an application,
 * Show that the function is family of types,
 * and the argument is an index.
 *)
interactive applyIntro (x: 'A -> 'B['x]) (bind{y. 'C['y]}) 'f 'a :
   [wf] sequent { <H> >- 'a in 'A } -->
   [wf] sequent { <H> >- 'f in (x: 'A -> 'B['x]) } -->
   [wf] sequent { <H> >- "type"{'B['a]} } -->
   [wf] sequent { <H>; y: 'B['a] >- "type"{'C['y]} } -->
   [main] sequent { <H>; y: 'B['a] >- 'C['y] } -->
   sequent { <H> >- 'C['f 'a] }

(*
 * To prove an application,
 * Show that the function is family of types,
 * and the argument is an index.
 *)
interactive independentApplyIntro ('A -> 'B) (bind{y. 'C['y]}) 'f 'a :
   [wf] sequent { <H> >- 'a in 'A } -->
   [wf] sequent { <H> >- 'f in ('A -> 'B) } -->
   [wf] sequent { <H>; y: 'B >- "type"{'C['y]} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   [main] sequent { <H>; y: 'B >- 'C['y] } -->
   sequent { <H> >- 'C['f 'a] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Add them as resources.
 *)
let applyT app = argfunT (fun i p ->
   if i = 0 then
      let f, a = dest_apply app in
      let goal_type =
         match get_with_arg p with
            Some t -> t
          | None -> infer_type p f
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
      let bind = var_subst_to_bind (Sequent.concl p) app in
         tac goal_type bind f a
   else
      raise (RefineError ("d_applyT", StringError "no elimination form")))

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
            if is_var_term f && SymbolSet.mem vars (dest_var f) then
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
let rec anyApplyT apps i =
   match apps with
      [app] ->
         applyT app i
    | app :: apps ->
         (applyT app i orelseT anyApplyT apps i)
    | [] ->
         raise (RefineError ("anyApplyT", StringError "no applications found"))

let autoApplyT = argfunT (fun i p ->
   let goal = Sequent.concl p in
      if is_type_term goal then
         raise (RefineError ("autoApplyT", StringError "don't apply to 'type' goals"))
      else
         let t = if i = 0 then Sequent.concl p else Sequent.nth_hyp p i in
         let apps = search_apply (free_vars_set t) t in
            anyApplyT apps i)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
