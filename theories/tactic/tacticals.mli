(*
 * Some basic tacticals.
 *)

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
val idT : tactic
val failT : tactic
val failWithT : string -> tactic
val nthAssumT : int -> tactic

(* Print timing information *)
val timingT : tactic -> tactic

(* Allow tactic only if no subgoals *)
val completeT : tactic -> tactic

(*
 * Repeatedly apply the tactic as long as there
 * is only one subgoal, and there is progress.
 *)
val progressT : tactic -> tactic
val repeatT : tactic -> tactic
val repeatForT : int -> tactic -> tactic
val seqOnSameConclT : tactic list -> tactic

(* Sequencing *)
val prefix_orelseT : tactic -> tactic -> tactic
val prefix_andalsoT : tactic -> tactic -> tactic
val prefix_orthenT : tactic -> tactic -> tactic
val firstT : tactic list -> tactic
val tryT : tactic -> tactic

val prefix_thenT : tactic -> tactic -> tactic
val prefix_thenLT : tactic -> tactic list -> tactic
val prefix_thenFLT : tactic -> (tactic_arg list -> tactic_value list) -> tactic
val prefix_then_OnFirstT : tactic -> tactic -> tactic
val prefix_then_OnLastT : tactic -> tactic -> tactic
val prefix_then_OnSameConclT : tactic -> tactic -> tactic

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

val addHiddenLabelT : string -> tactic
val removeHiddenLabelT : tactic
val keepingLabelT : tactic -> tactic
val ifLabLT : (string * tactic) list -> tactic
val ifLabT : string -> tactic -> tactic -> tactic

(*
 * Label tacticals.
 *)
val prefix_thenLabLT : tactic -> (string * tactic) list -> tactic
val prefix_thenMT : tactic -> tactic -> tactic
val prefix_thenMLT : tactic -> tactic list -> tactic
val prefix_thenAT : tactic -> tactic -> tactic
val prefix_thenALT : tactic -> tactic list -> tactic
val prefix_thenWT : tactic -> tactic -> tactic
val prefix_thenET : tactic -> tactic -> tactic
val prefix_thenPT : tactic -> tactic -> tactic

val repeatMT : tactic -> tactic
val repeatMForT : int -> tactic -> tactic
val seqOnMT : tactic list -> tactic
val seqT : tactic list -> tactic
val completeMT : tactic -> tactic
val labProgressT : tactic -> tactic

(*
 * Hyp and Clausal tactics.
 *)
val onClauseT : int -> (int -> tactic) -> tactic
val onHypT : int -> (int -> tactic) -> tactic
val onConclT : (int -> tactic) -> tactic

val onClausesT : int list -> (int -> tactic) -> tactic
val onHypsT : int list -> (int -> tactic) -> tactic

val onMClausesT : int list -> (int -> tactic) -> tactic
val onMHypsT : int list -> (int -> tactic) -> tactic

val onAllHypsT : (int -> tactic) -> tactic
val onAllClausesT : (int -> tactic) -> tactic
val tryOnAllHypsT : (int -> tactic) -> tactic
val tryOnAllClausesT : (int -> tactic) -> tactic

val onAllMHypsT : (int -> tactic) -> tactic
val onAllMClausesT : (int -> tactic) -> tactic
val tryOnAllMHypsT : (int -> tactic) -> tactic
val tryOnAllMClausesT : (int -> tactic) -> tactic

val onSomeHypT : (int -> tactic) -> tactic
val onVarT : string -> (int -> tactic) -> tactic

(*
 * General argument functions.
 *)
val withTermT : string -> term -> tactic -> tactic
val withTypeT : string -> term -> tactic -> tactic
val withBoolT : string -> bool -> tactic -> tactic
val withIntT : string -> int -> tactic -> tactic
val withSubstT : term_subst -> tactic -> tactic
val withTacticT : string -> tactic -> tactic -> tactic

(*
 * Specific argument functions.
 *)
val withT : term -> tactic -> tactic
val usingT : term_subst -> tactic -> tactic
val atT : term -> tactic -> tactic
val selT : int -> tactic -> tactic
val thinningT : bool -> tactic -> tactic

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
