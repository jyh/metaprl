(*
 * Prove propositional theorems, from Dyckhoff.
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

extends Itt_logic

open Printf
open Mp_debug

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Conversionals
open Tactic_type.Tacticals

open Base_auto_tactic
open Base_dtactic
open Var

open Itt_logic
open Itt_struct

let debug_prop_decide =
  create_debug (**)
     { debug_name = "prop_decide";
       debug_description = "show propDecide operations";
       debug_value = false
     }

(* Like onSomeHyp, but works backwards. *)
let revOnSomeHypT tac p =
   let rec aux i =
      if i = 1 then
         tac i
      else if i > 1 then
         tac i orelseT (aux (pred i))
      else
         idT
   in
      aux (Sequent.hyp_count p) p

(* Operate on all non-wf subgoals *)
let ifNotWT tac p =
   (if (Sequent.label p) = "wf" then
       idT
    else
       tac) p

(* Term classes *)
let is_imp_and_term term =
   is_implies_term term & is_and_term (term_subterm term (make_address [0]))

let is_imp_or_term term =
   is_implies_term term & is_or_term (term_subterm term (make_address [0]))

let is_imp_imp_term term =
   is_implies_term term & is_implies_term (term_subterm term (make_address [0]))

interactive imp_and_rule 'H :
   sequent [squash] { 'H; x: "and"{'C; 'D} => 'B; 'J['x] >- "type"{'C} } -->
   sequent [squash] { 'H; x: "and"{'C; 'D} => 'B; 'J['x] >- "type"{'D} } -->
   sequent ['ext] { 'H; x: "and"{'C; 'D} => 'B; 'J['x];
                     u: 'C => 'D => 'B >- 'T['x] } -->
   sequent ['ext] { 'H; x: "and"{'C; 'D} => 'B; 'J['x] >- 'T['x] }

interactive imp_or_rule 'H :
   sequent [squash] { 'H; x: "or"{'C; 'D} => 'B; 'J['x] >- "type"{'C} } -->
   sequent [squash] { 'H; x: "or"{'C; 'D} => 'B; 'J['x] >- "type"{'D} } -->
   sequent ['ext] { 'H; x: "or"{'C; 'D} => 'B; 'J['x];
                     u: 'C => 'B; v: 'D => 'B >- 'T['x] } -->
   sequent ['ext] { 'H; x: "or"{'C; 'D} => 'B; 'J['x] >- 'T['x] }

interactive imp_imp_rule 'H :
   sequent [squash] { 'H; x: "implies"{'C; 'D} => 'B; 'J['x] >- "type"{'C} } -->
   sequent [squash] { 'H; x: "implies"{'C; 'D} => 'B; 'J['x] >- "type"{'D} } -->
   sequent ['ext] { 'H; x: "implies"{'C; 'D} => 'B; 'J['x];
                     u: 'D => 'B >- 'T['x] } -->
   sequent ['ext] { 'H; x: "implies"{'C; 'D} => 'B; 'J['x] >- 'T['x] }

(* Create a tactic for the X-implication-elimination. *)
let d_and_impT i =
   imp_and_rule i
      thenLT [addHiddenLabelT "wf";
              addHiddenLabelT "wf";
              thinT i]

let d_or_impT i =
   imp_or_rule i
      thenLT [addHiddenLabelT "wf";
              addHiddenLabelT "wf";
              thinT i]

let d_imp_impT i =
   imp_and_rule i
      thenLT [addHiddenLabelT "wf";
              addHiddenLabelT "wf";
              thinT i]

(* Try to decompose a hypothesis *)
let rec decompPropDecideHypT count i p =
   (let term = Sequent.nth_hyp p i in
       if is_false_term term then
          dT i
       else if is_and_term term or is_or_term term then
          dT i thenT ifNotWT (internalPropDecideT count)
       else if is_imp_and_term term then
          (* {C & D => B} => {C => D => B} *)
          d_and_impT i thenT ifNotWT (internalPropDecideT count)
       else if is_imp_or_term term then
          (* {C or D => B} => {(C => B) & (D => B)} *)
          d_or_impT i thenT ifNotWT (internalPropDecideT count)
       else if is_imp_imp_term term then
          (* {(C => D) => B} => {D => B} *)
          d_imp_impT i thenT ifNotWT (internalPropDecideT count)
       else if is_implies_term term then
          dT i thenT thinT i thenT ifNotWT (internalPropDecideT count)
       else
          (* Nothing recognized, try to see if we're done. *)
          nthHypT i) p

(* Decompose the goal *)
and decompPropDecideConclT count p =
   if !debug_prop_decide then
      begin
         eprintf "decompPropDecideConclT: %a%t" Refiner.Refiner.Term.debug_print (Sequent.concl p) eflush
      end;
   (let goal = Sequent.concl p in
       if is_or_term goal then
          (selT 1 (dT 0) thenT ifNotWT (internalPropDecideT count))
          orelseT (selT 2 (dT 0) thenT ifNotWT (internalPropDecideT count))
       else if is_and_term goal or is_implies_term goal then
          dT 0 thenT ifNotWT (internalPropDecideT count)
       else
          trivialT) p

(* Prove the proposition - internal version that does not handle negation *)
and internalPropDecideT count p =
   if !debug_prop_decide then
      eprintf "propDecideT: %d: %a%t" count debug_print (Sequent.goal p) eflush;
   let count = succ count in
      (revOnSomeHypT (decompPropDecideHypT count) orelseT decompPropDecideConclT count) p

(* Convert all "not X" terms to "X => False" *)
let notToImpliesFalseC =
   sweepUpC (unfold_not thenC fold_implies thenC (addrC [1] fold_false))

(*
 * Toplevel tactic:
 * Unfold all negations, then run Dyckoff's algorithm.
 *)
let propDecideT =
   onAllClausesT (fun i -> tryT (rw notToImpliesFalseC i))
   thenT internalPropDecideT 0

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
