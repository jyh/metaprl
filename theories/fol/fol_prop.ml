(*
 * Definition of typehood.
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

(* Operators in the logic *)
extends Fol_type
extends Fol_false
extends Fol_true
extends Fol_and
extends Fol_or
extends Fol_implies
extends Fol_not
extends Fol_struct

(* An example theorem *)
interactive distrib_or :
   [wf] sequent ['ext] { <H> >- "type"{'A} } -->
   [wf] sequent ['ext] { <H> >- "type"{'B} } -->
   [wf] sequent ['ext] { <H> >- "type"{'C} } -->
   sequent ['ext] { <H> >- (('A or 'B) => 'C) => (('A => 'C) & ('B => 'C)) }

(* Automation *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Base_dtactic
open Base_auto_tactic
open Fol_not
open Fol_struct

(* Refinement of implication *)
interactive imp_and_rule 'H :
   [wf] sequent['ext] { <H>; x: ('C & 'D) => 'B; <J> >- "type"{'C}} -->
   [wf] sequent['ext] { <H>; x: ('C & 'D) => 'B; <J> >- "type"{'D}} -->
   [main] sequent['ext] { <H>; <J>; u: 'C => 'D => 'B >- 'T} -->
   sequent['ext] { <H>; x: ('C & 'D) => 'B; <J> >- 'T}

interactive imp_or_rule 'H :
   [wf] sequent['ext] { <H>; x: ('C or 'D) => 'B; <J> >- "type"{'C}} -->
   [wf] sequent['ext] { <H>; x: ('C or 'D) => 'B; <J> >- "type"{'D}} -->
   [main] sequent['ext] { <H>; <J>; u: 'C => 'B; v: 'D => 'B >- 'T} -->
   sequent['ext] { <H>; x: ('C or 'D) => 'B; <J> >- 'T}

interactive imp_imp_rule 'H :
   [wf] sequent['ext] { <H>; x: ('C => 'D) => 'B; <J> >- "type"{'C}} -->
   [wf] sequent['ext] { <H>; x: ('C => 'D) => 'B; <J> >- "type"{'D}} -->
   [main] sequent['ext] { <H>; <J>; u: 'D => 'B >- 'T} -->
   sequent['ext] { <H>; x: ('C => 'D) => 'B; <J> >- 'T}

let d_and_impT = imp_and_rule
let d_or_impT = imp_or_rule
let d_imp_impT = imp_and_rule

(* Term operations *)
let false_opname = opname_of_term << "false" >>
let is_false_term = is_no_subterms_term false_opname

let and_opname = opname_of_term << 'A & 'B >>
let is_and_term = is_dep0_dep0_term and_opname

let or_opname = opname_of_term << 'A or 'B >>
let is_or_term = is_dep0_dep0_term or_opname

let implies_opname = opname_of_term << 'A => 'B >>
let is_implies_term = is_dep0_dep0_term implies_opname

let is_imp_and_term term =
   is_implies_term term & is_and_term (fst (two_subterms term))

let is_imp_or_term term =
   is_implies_term term & is_or_term (fst (two_subterms term))

let is_imp_imp_term term =
   is_implies_term term & is_implies_term (fst (two_subterms term))

(* This tactic is convenient *)
let ifNotWT tac p =
   (if (Sequent.label p) = "wf" then
       idT
    else
       tac) p

(* Try to decompose a hypothesis *)
let rec decompPropDecideHypT i p =
   let i = Sequent.get_pos_hyp_num p i in
   (let term = Sequent.nth_hyp p i in
       if is_false_term term then
          dT i
       else if is_and_term term or is_or_term term then
          dT i thenT ifNotWT internalPropDecideT
       else if is_imp_and_term term then
          (* {C & D => B} => {C => D => B} *)
          d_and_impT i thenT ifNotWT internalPropDecideT
       else if is_imp_or_term term then
          (* {C or D => B} => {(C => B) & (D => B)} *)
          d_or_impT i thenT ifNotWT internalPropDecideT
       else if is_imp_imp_term term then
          (* {(C => D) => B} => {D => B} *)
          d_imp_impT i thenT ifNotWT internalPropDecideT
       else if is_implies_term term then
          dT i thenT thinT i thenT ifNotWT internalPropDecideT
       else
          (* Nothing recognized, try to see if we're done. *)
          nthHypT i) p

(* Decompose the goal *)
and decompPropDecideConclT p =
   (let goal = Sequent.concl p in
       if is_or_term goal then
          (selT 1 (dT 0) thenT ifNotWT internalPropDecideT)
          orelseT (selT 2 (dT 0) thenT ifNotWT internalPropDecideT)
       else if is_and_term goal or is_implies_term goal then
          dT 0 thenT ifNotWT internalPropDecideT
       else
          trivialT) p

(* Internal version that does not handle negation *)
and internalPropDecideT p =
   (onSomeHypT decompPropDecideHypT orelseT decompPropDecideConclT) p

let propDecideT =
   onAllClausesT (fun i -> tryT (rw (sweepUpC unfold_not) i))
   thenT internalPropDecideT

(* Simple tactic for proving typehood *)
let thinAllT i j p =
   let rec tac j =
      if j < i then
         idT
      else
         thinT j thenT tac (pred j)
   in
      tac j p

let proveTypeT p =
   (thinAllT 2 (Sequent.hyp_count p) thenT trivialT) p

(* Try the example again *)
interactive distrib_or2 :
   [wf] sequent ['ext] { <H> >- "type"{'A} } -->
   [wf] sequent ['ext] { <H> >- "type"{'B} } -->
   [wf] sequent ['ext] { <H> >- "type"{'C} } -->
   sequent ['ext] { <H> >- (('A or 'B) => 'C) => (('A => 'C) & ('B => 'C)) }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
