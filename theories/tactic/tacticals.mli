(*
 * Some basic tacticals.
 *
 * $Log$
 * Revision 1.1  1997/04/28 15:52:45  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.1  1996/09/25 22:52:07  jyh
 * Initial "tactical" commit.
 *
 *)

open Term
open Refine
open Tactic_type

axiom id : 'T --> 'T

(* Trivial tactics *)
val idT : tactic
val failT : tactic

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

val prefix_thenT : tactic -> tactic -> tactic
val prefix_thenLT : tactic -> tactic list -> tactic
val prefix_thenFLT : tactic ->
       (tactic_arg list -> safe_tactic list) ->
       tactic
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
 * Arguments.
 *)
val withT : term -> tactic -> tactic
val newT : string list -> tactic -> tactic
val usingT : (string * term) list -> tactic -> tactic
val atT : term -> tactic -> tactic
val selT : int -> tactic -> tactic
val notThinningT : tactic -> tactic
val thinningT : tactic -> tactic

val get_int_arg : int -> tactic_arg -> int
val get_int_args : tactic_arg -> int list
val get_var_arg : int -> tactic_arg -> string
val get_var_args : tactic_arg -> string list
val get_term_arg : int -> tactic_arg -> term
val get_term_args : tactic_arg -> term list
val get_thinning_arg : tactic_arg -> bool

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
