(*
 * Some basic tacticals.
 *)

open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Tactic_type

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

val get_term_arg    : tactic_arg -> string -> term
val get_type_arg    : tactic_arg -> string -> term
val get_int_arg     : tactic_arg -> string -> int
val get_bool_arg    : tactic_arg -> string -> bool
val get_subst_arg   : tactic_arg -> term_subst
val get_tactic_arg  : tactic_arg -> string -> tactic

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
 * $Log$
 * Revision 1.7  1998/06/22 19:46:48  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.6  1998/06/15 22:33:50  jyh
 * Added CZF.
 *
 * Revision 1.5  1998/06/09 20:53:04  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.4  1998/06/03 22:20:05  jyh
 * Nonpolymorphic refiner.
 *
 * Revision 1.3  1998/05/28 13:48:42  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.2  1997/08/06 16:18:55  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
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
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
