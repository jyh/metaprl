(*
 * Some basic tacticals.
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

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine

open Sequent

(* Types *)
type tactic = Tactic_type.tactic

(* Basic refinement *)
val refine : tactic -> tactic_arg -> tactic_arg list * extract
val compose : extract -> extract list -> extract
val term_of_extract : Refine.refiner -> extract -> term list -> term

(* Trivial tactics *)
topval idT : tactic
topval failT : tactic
topval failWithT : string -> tactic
topval nthAssumT : int -> tactic

(* Print timing information *)
topval timingT : tactic -> tactic
val finalT : (unit -> unit) -> tactic

(* Allow tactic only if no subgoals *)
topval completeT : tactic -> tactic

(*
 * Repeatedly apply the tactic as long as there
 * is only one subgoal, and there is progress.
 *)
topval progressT : tactic -> tactic
topval repeatT : tactic -> tactic
topval repeatForT : int -> tactic -> tactic
topval seqOnSameConclT : tactic list -> tactic

(* Sequencing *)
topval prefix_orelseT : tactic -> tactic -> tactic
topval prefix_andalsoT : tactic -> tactic -> tactic
topval prefix_orthenT : tactic -> tactic -> tactic
topval firstT : tactic list -> tactic
topval tryT : tactic -> tactic

topval prefix_thenT : tactic -> tactic -> tactic
topval prefix_thenLT : tactic -> tactic list -> tactic
val prefix_thenFLT : tactic -> (tactic_arg list -> tactic_value list) -> tactic
topval prefix_then_OnFirstT : tactic -> tactic -> tactic
topval prefix_then_OnLastT : tactic -> tactic -> tactic
topval prefix_then_OnSameConclT : tactic -> tactic -> tactic

(*
 * Conditionals.
 *)
val ifT : (tactic_arg -> bool) -> tactic -> tactic -> tactic
val ifOnConclT : (term -> bool) -> tactic -> tactic -> tactic
val ifOnHypT : (term -> bool) -> (int -> tactic) -> (int -> tactic) -> int -> tactic
val ifThenT : (term -> bool) -> tactic -> tactic
val ifThenOnConclT : (term -> bool) -> tactic -> tactic
val ifThenOnHypT : (term -> bool) -> (int -> tactic) -> int -> tactic

val whileT : (term -> bool) -> tactic -> tactic
val untilT : (term -> bool) -> tactic -> tactic

(*
 * Label tactics.
 *)
val main_labels : string list
val predicate_labels : string list

topval addHiddenLabelT : string -> tactic
topval removeHiddenLabelT : tactic
topval keepingLabelT : tactic -> tactic
val ifLabLT : (string * tactic) list -> tactic
topval ifLabT : string -> tactic -> tactic -> tactic

(*
 * Label tacticals.
 *)
val prefix_thenLabLT : tactic -> (string * tactic) list -> tactic
topval prefix_thenMT : tactic -> tactic -> tactic
topval prefix_thenMLT : tactic -> tactic list -> tactic
topval prefix_thenAT : tactic -> tactic -> tactic
topval prefix_thenALT : tactic -> tactic list -> tactic
topval prefix_thenWT : tactic -> tactic -> tactic
topval prefix_thenET : tactic -> tactic -> tactic
topval prefix_thenPT : tactic -> tactic -> tactic

topval repeatMT : tactic -> tactic
topval repeatMForT : int -> tactic -> tactic
topval seqOnMT : tactic list -> tactic
topval seqT : tactic list -> tactic
topval completeMT : tactic -> tactic
topval labProgressT : tactic -> tactic

(*
 * Hyp and Clausal tactics.
 *)
topval onClauseT : int -> (int -> tactic) -> tactic
topval onHypT : int -> (int -> tactic) -> tactic
topval onConclT : (int -> tactic) -> tactic

topval onClausesT : int list -> (int -> tactic) -> tactic
topval onHypsT : int list -> (int -> tactic) -> tactic

topval onMClausesT : int list -> (int -> tactic) -> tactic
topval onMHypsT : int list -> (int -> tactic) -> tactic

topval onAllHypsT : (int -> tactic) -> tactic
topval onAllClausesT : (int -> tactic) -> tactic
topval tryOnAllHypsT : (int -> tactic) -> tactic
topval tryOnAllClausesT : (int -> tactic) -> tactic

topval onAllMHypsT : (int -> tactic) -> tactic
topval onAllMClausesT : (int -> tactic) -> tactic
topval tryOnAllMHypsT : (int -> tactic) -> tactic
topval tryOnAllMClausesT : (int -> tactic) -> tactic

topval onSomeAssumT : (int -> tactic) -> tactic
topval onSomeHypT : (int -> tactic) -> tactic
topval onVarT : string -> (int -> tactic) -> tactic

(*
 * General argument functions.
 *)
topval withTermT : string -> term -> tactic -> tactic
topval withTypeT : string -> term -> tactic -> tactic
topval withBoolT : string -> bool -> tactic -> tactic
topval withIntT : string -> int -> tactic -> tactic
val withSubstT : term_subst -> tactic -> tactic
topval withTacticT : string -> tactic -> tactic -> tactic

(*
 * Specific argument functions.
 *)
topval withT : term -> tactic -> tactic
val usingT : term_subst -> tactic -> tactic
topval atT : term -> tactic -> tactic
topval selT : int -> tactic -> tactic
topval thinningT : bool -> tactic -> tactic

val get_with_arg : tactic_arg -> term
val get_univ_arg : tactic_arg -> term
val get_sel_arg : tactic_arg -> int
val get_thinning_arg : tactic_arg -> bool

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
