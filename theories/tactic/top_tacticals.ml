(*!
 * @begin[spelling]
 * OnFirstT OnLastT OnSameConclT addHiddenLabelT cutT dT failT failWithT
 * firstT idT ifLabT keepingLabelT nthAssumT onAllClausesT onClauseT
 * onClausesT onConclT onHypT onHypsT onSomeHypT onVarT orelseT progressT
 * removeHiddenLabelT repeatForT repeatMT repeatT whileProgressT untilFailT
 * whileProgressMT untilFailMT selT
 * seqOnSameConclT seqT tactical thenAT thenET thenMT thenT thenWT timingT
 * tryT withBoolT withIntT withT withTypeT
 *
 * tac wf
 * @end[spelling]
 *
 * @begin[doc]
 * @theory[Top_tacticals]
 *
 * The @tt{Top_tacticals} module defines the primitive
 * tactics and tacticals provided by the @MetaPRL prover.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * @email{jyh@cs.caltech.edu}
 *
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Mptop

(*!************************************************************************
 * @begin[doc]
 * @thysection{Primitive tactics}
 *
 * @begin[description]
 * @item{@tactic[idT];
 * The @tt{idT} tactic is the @emph{identity}.
 *
 * $$
 * @rulebox{idT; ;
 *   @sequent{ext; H; T};
 *   @sequent{ext; H; T}}
 * $$}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let idT = Tactic_type.Tacticals.idT

(*!
 * @begin[doc]
 * @begin[description]
 * @item{@tactic[cutT];
 * The @tt{cutT} tactic implements primitive lemma-instantiation.
 *
 * $$
 * @rulebox{cutT; T_1;
 *   @sequent{ext; H; T_1}@cr
 *   @sequent{ext; {H; x@colon T_1}; T_2};
 *   @sequent{ext; H; T_2}}
 * $$}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let cutT = Tactic_type.Tacticals.cutT

(*!
 * @begin[doc]
 * @begin[description]
 * @item{@tactic[failT], @tactic[failwithT];
 * The @tt{failT} tactic always fails, and the @tt{failWithT} fails
 * with a specific message.}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let failT = Tactic_type.Tacticals.failT
let failWithT = Tactic_type.Tacticals.failWithT

(*!
 * @begin[doc]
 * @begin[description]
 * @item{@tactic[nthAssumT];
 * The @tt{nthAssumT} tactic proves a goal by @emph{assumption}.
 * Technically, an assumption is a subgoal of the theorem being proved.
 * The assumption must be syntactically identical to the goal.
 *
 * $$
 * @rulebox{nthAssumT; i;
 *  @cdot;
 *  @sequent{ext; H_1; T_1} @i{(Assumption@space 1)}@cr
 *  @ldots@cr
 *  @sequent{ext; H_i; T_i} @i{(Assumption@space @i{i})}@cr
 *  @ldots@cr
 *  @sequent{ext; H_n; T_n} @i{(Assumption@space @i{n})}@cr
 *  @hline
 *  @sequent{ext; H_i; T_i}}
 * $$}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let nthAssumT = Tactic_type.Tacticals.nthAssumT

(*!************************************************************************
 * @begin[doc]
 * @thysection{Tacticals}
 *
 * @begin[description]
 * @item{@tactic[thenT], @tactic[orelseT];
 * There are several tacticals to manage proof search.  The basic
 * tacticals are @tt{thenT} and @tt{orelseT}, both @emph{infix}
 * tacticals.  The tactic @tt{$@i{tac}_1$ thenT $@i{tac}_2$}
 * first applies $@i{tac}_1$ to the goal, and then applies $@i{tac}_2$
 * to @emph{all} of the subgoals.  It fails if either tactic fails
 * on any of the subgoals.  The tactic @tt{$@i{tac}_1$ orelseT $@i{tac}_2$}
 * first applies $@i{tac}_1$.  If it succeeds, $@i{tac}_2$ is ignored.
 * Otherwise, $@i{tac}_2$ is applied to the original goal.}
 *
 * @item{@tactic[firstT];
 * The @tt{firstT} tactical is a variant of @tt{orelseT}.  It takes
 * a list of tactics @tt{$[@i{tac}_1; @ldots; @i{tac}_n]$} to be applied
 * in order until the first one succeeds.  It fails if all of the argument
 * tactics fail.  It is equivalent to (@tt{$@i{tac_1}$ orelseT $@cdots$
 * orelseT $@i{tac}_n$}).}
 *
 * @item{@tactic[seqT], @tactic[seqOnSameConclT];
 * The @tt{seqT} is the universal form of the @tt{firstT} tactical.
 * The (@tt{seqT $[@i{tac}_1; @ldots; @i{tac}_n]$}) tactic is equivalent to
 * (@tt{$@i{tac}_1$ thenT $@cdots$ thenT $@i{tac}_n$}).  The @tt{seqOnSameConclT}
 * tactic is the same as @tt{seqT} except that is selects only those subgoals
 * that have the same conclusion as the current goal.}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let prefix_orelseT = Tactic_type.Tacticals.prefix_orelseT
let prefix_andalsoT = Tactic_type.Tacticals.prefix_andalsoT
let prefix_orthenT = Tactic_type.Tacticals.prefix_orthenT
let firstT = Tactic_type.Tacticals.firstT
let prefix_thenT = Tactic_type.Tacticals.prefix_thenT
let prefix_thenLT = Tactic_type.Tacticals.prefix_thenLT
let seqT = Tactic_type.Tacticals.seqT
let seqOnSameConclT = Tactic_type.Tacticals.seqOnSameConclT

(*!
 * @begin[doc]
 * @begin[description]
 * @item{@tactic[then_OnFirstT],
 *       @tactic[then_OnLastT],
 *       @tactic[then_OnSameConclT];
 * There are also several tactics that apply to selected subgoals by number.
 * The use of these tactics is discouraged in favor of selecting tactics
 * by label (discussed below).
 *
 * The @tt{$@i{tac}_1$ then_OnFirstT $@i{tac}_2$} applies $@i{tac}_1$
 * to the goal, and then applies $@i{tac}_2$ to the @emph{first} subgoal
 * that is generated.  The @tt{then_OnLastT} selects the last subgoal,
 * and the @tt{then_OnSameConclT} tactic chooses the subgoal with the
 * same conclusion as the current goal.}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let prefix_then_OnFirstT = Tactic_type.Tacticals.prefix_then_OnFirstT
let prefix_then_OnLastT = Tactic_type.Tacticals.prefix_then_OnLastT
let prefix_then_OnSameConclT = Tactic_type.Tacticals.prefix_then_OnSameConclT

(*!
 * @begin[doc]
 * @begin[description]
 * @item{@tactic[timingT];
 * The @tt{timingT} tactical applies its argument,
 * and prints timing information useful for tactic profiling.
 *
 * $$
 * @rulebox{idT; ;
 *   @sequent{ext; H; T};
 *   @sequent{ext; H; T}}
 * $$
 *
 * @code{User time 0.000000; System time 0.000000; Real time 0.001778}}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let timingT = Tactic_type.Tacticals.timingT

(*!
 * @begin[doc]
 * @begin[description]
 * @item{@tactic[tryT], @tactic[completeT];
 * The @tt{tryT} tactical applies its argument, and performs
 * the identity if the tactic fails.  The tactic (@tt{tryT} @i{tac})
 * is equivalent to (@i{tac} @tt{orelseT idT}).}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let tryT = Tactic_type.Tacticals.tryT
let completeT = Tactic_type.Tacticals.completeT

(*!
 * @begin[doc]
 * @begin[description]
 * @item{@tactic[progressT];
 * The (@tt{progressT} $@i{tac}$) tactic applies it argument and fails
 * if either 1) $@i{tac}$ fails, or $@i{tac}$ failed to make ``progress''
 * by generating subgoals that differ from the current goal.}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let progressT = Tactic_type.Tacticals.progressT

(*!
 * @begin[doc]
 * @begin[description]
 * @item{@tactic[whileProgressT], @tactic[untilFailT], @tactic[repeatT], @tactic[repeatForT];
 * The (@tt{untilFailT} $@i{tac}$) tactic applies the argument $@i{tac}$
 * repeatedly to the current goal and all of the generated subgoals until
 * an application of $@i{tac}$ fails. This is the same as @tt{REPEAT} tactical in Nuprl.
 * Note that the (@tt{untilFailT} $@i{tac}$) tactic
 * collects all exceptions generated by $@i{tac}$ and it never fails itself.
 *
 * The (@tt{whileProgressT} $@i{tac}$) tactic repeatedly executes the given tactic on all subgoals
 * while there is a progress. If $@i{tac}$ fails, then @tt{whileProgressT} also fails.
 *
 *
 * The (@tt{repeatT} $@i{tac}$) tactic is equal to  (@tt{whileProgressT tryT} $@i{tac}$).
 * It repeats the application of its argument until it fails or no more progress is made.
 *
 * The (@tt{repeatForT} $i$ $@i{tac}$) repeatedly execute the given tactic  $@i{tac}$ on all subgoals
 * until the depth $i$ is reached. If $@i{tac}$ fails, then @tt{repeatForT} also fails.
 * }
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let repeatT = Tactic_type.Tacticals.repeatT
let whileProgressT = Tactic_type.Tacticals.whileProgressT
let untilFailT = Tactic_type.Tacticals.untilFailT
let repeatForT = Tactic_type.Tacticals.repeatForT

(*!************************************************************************
 * @begin[doc]
 * @thysection{Tactic arguments}
 *
 * Tactics and rules may require arguments of various types (such as numbers, strings,
 * terms, or even other tactics).  The proof structure allows the proof tree to
 * be annotated with these arguments, and the arguments are inherited down
 * the proof tree until they are removed.  This allows the proof to act as a
 * temporary environment for communication between tactics.
 * The following tactics apply
 * temporary annotations.
 *
 * @begin[description]
 * @item{@tactic[withT], @tactic[withTypeT], @tactic[withBoolT], @tactic[withIntT];
 * {The (@tt{withT} @i{term tac}) tactic adds a term annotation to the
 * tree@; applies @i{tac}@; and then removes the term annotation from all of
 * the subgoals.  The @tt{withTypeT} adds a ``type'' annotation (the type is
 * expressed as a term).  The @tt{withBoolT} and @tt{withIntT} add Boolean and
 * integer annotations.}}
 *
 * @item{@tactic[selT];
 * There is one more tactical that is frequently
 * used in the @MetaPRL logics: by convention the @tt{selT} tactical is used to
 * ``select'' among several alternate methods of proof.  For example, in proving
 * a disjunction (Section @reftheory[Itt_logic]) it is necessary to select the
 * branch of the disjunct.
 *
 * $$
 * @rulebox{selT; 2@space (@tt{dT}@space 0);
 *   @sequent{ext; {H; x@colon T_2; J}; T_1@space @i{Type}}@cr
 *   @sequent{ext; {H; x@colon T_2; J}; T_2};
 *   @sequent{ext; {H; x@colon T_2; J}; T_1 @vee T_2}}
 * $$}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let withTermT = Tactic_type.Tacticals.withTermT
let withTypeT = Tactic_type.Tacticals.withTypeT
let withBoolT = Tactic_type.Tacticals.withBoolT
let withIntT = Tactic_type.Tacticals.withIntT
let withT = Tactic_type.Tacticals.withT
let withTermsT = Tactic_type.Tacticals.withTermsT
let atT = Tactic_type.Tacticals.atT
let selT = Tactic_type.Tacticals.selT
let altT = Tactic_type.Tacticals.altT
let thinningT = Tactic_type.Tacticals.thinningT
let doNotThinT = thinningT false

(*!************************************************************************
 * @begin[doc]
 * @thysection{Clause selection}
 *
 * The following tactics are intended for use in a single-conclusion sequent calculus.
 * A sequent $@sequent{ext; {x_1@colon T_1; @cdots; x_n@colon T_n}; C}$ has
 * $n + 1$ @emph{clauses}.  The hypotheses are clauses $1, @ldots, n$ and the conclusion
 * is clause $0$.
 *
 * @begin[description]
 * @item{@tactic[onClauseT], @tactic[onHypT], @tactic[onConclT];
 * The (@tt{onClauseT} $i$ @i{tac}) tactic applies the argument tactic with
 * integer argument $i$ (it is equivalent to @i{tac} $i$).  The @tt{onHypT}
 * restricts the integer argument to be a valid hypothesis number, and the
 * (@tt{onConclT} @i{tac}) tactical applies its argument tactic with
 * argument $0$.}
 *
 * @item{@tactic[onVarT];
 * The (@tt{onVarT} @i{tac}) applies its argument with the number
 * of the hypothesis labeled with variable $v$.}
 *
 * @item{@tactic[onClausesT], @tactic[onHypsT];
 * The @tt{onClausesT} and @tt{onHypsT} take a list of clause numbers.
 * The (@tt{onClausesT} $[i_1; @cdots; i_n]$ @i{tac}) is equivalent to
 * (@tt{@i{tac} $i_1$ thenT $@cdots$ thenT @i{tac} $i_n$ thenT @i{tac} $0$}).  The
 * @tt{onHypsT} does the same, but it requires that the indices correspond
 * to valid hypothesis numbers.}
 *
 * @item{@tactic[onAllClausesT], @tactic[onAllHypsT];
 * The (@tt{onAllClausesT} @i{tac}) applies the argument tactic to all the clauses,
 * including all the hypothesis and the conclusion.  The @tt{onHypsT} applies the
 * argument only to the hypotheses.}
 *
 * @item{@tactic[onAllAssumT];
 * The (@tt{onAllAssumT} @i{tac}) applies the argument tactic to all the assumptions.
  ,
 * including all the hypothesis and the conclusion.  The @tt{onHypsT} applies the
 * argument only to the hypotheses.}
 *
 * @item{@tactic[onSomeHypT];
 * The (@tt{onSomeHypT} @i{tac}) applies the argument tactic to the
 * hypotheses from the last to the first, returning once an application
 * succeeds.  The (@tt{onSomeHypT} @i{tac}) is equivalent to
 * (@tt{@i{tac} $n$ orelseT $@cdots$ orelseT @i{tac} $1$}).}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let onClauseT = Tactic_type.Tacticals.onClauseT
let onHypT = Tactic_type.Tacticals.onHypT
let onConclT = Tactic_type.Tacticals.onConclT
let onClausesT = Tactic_type.Tacticals.onClausesT
let onHypsT = Tactic_type.Tacticals.onHypsT
let onMClausesT = Tactic_type.Tacticals.onMClausesT
let onMHypsT = Tactic_type.Tacticals.onMHypsT
let onAllHypsT = Tactic_type.Tacticals.onAllHypsT
let onAllClausesT = Tactic_type.Tacticals.onAllClausesT
let tryOnHypsT = Tactic_type.Tacticals.tryOnHypsT
let tryOnClausesT = Tactic_type.Tacticals.tryOnClausesT
let tryOnAllHypsT = Tactic_type.Tacticals.tryOnAllHypsT
let tryOnAllClausesT = Tactic_type.Tacticals.tryOnAllClausesT
let onAllMHypsT = Tactic_type.Tacticals.onAllMHypsT
let onAllMClausesT = Tactic_type.Tacticals.onAllMClausesT
let onAllAssumT = Tactic_type.Tacticals.onAllMAssumT
let onAllMAssumT = Tactic_type.Tacticals.onAllMAssumT
let tryOnAllMHypsT = Tactic_type.Tacticals.tryOnAllMHypsT
let tryOnAllMClausesT = Tactic_type.Tacticals.tryOnAllMClausesT
let onSomeAssumT = Tactic_type.Tacticals.onSomeAssumT
let onSomeHypT = Tactic_type.Tacticals.onSomeHypT
let onVarT = Tactic_type.Tacticals.onVarT

(*!************************************************************************
 * @begin[doc]
 * @thysection{Labels}
 *
 * Each node in a proof tree has a @emph{label}.  The labels have no logical
 * meaning, but they are frequently used to provide an informal description
 * of the kind of subgoal.  A label can be any string, but there are three
 * commonly used labels: ``main'' identifies the main steps of a proof,
 * ``antecedent'' identifies nodes that are assumptions that have to be
 * proved, and ``wf'' identifies nodes that require well-formedness reasoning.
 *
 * @begin[description]
 * @item{@tactic[addHiddenLabelT], @tactic[removeHiddenLabelT], @tactic[keepingLabelT];
 * There are three tacticals that directly manipulate the label.
 * The (@tt{addHiddenLabelT} ``label'') tactic assigns the label to
 * the current goal, the @tt{removeHiddenLabelT} tactic assigns
 * the label ``main'', and the (@tt{keepingLabelT} $@i{tac}$) applies
 * the tactic $@i{tac}$ and assigns the label of the current goal
 * to all of the remaining subgoals.  The ``@tt{Hidden}'' is of historical
 * significance only@; the labels are hidden only in the sense that they
 * have no logical significance.}
 *
 * @item{@tactic[ifLabT];
 * In addition to manipulating the labels, there are several tacticals
 * that take advantage of the label to apply tactics selectively.  The
 * (@tt{ifLabT} $l$ $@i{tac1}$ $@i{tac2}$) applies the tactic $@i{tac1}$ if
 * the current goal has label $l$, otherwise it applies the  tactic $@i{tac2}$.}
 *
 * @item{@tactic[thenMT], @tactic[thenET], @tactic[thenWT], @tactic[thenAT];
 * The (infix) @tt{thenMT}, @tt{thenET}, and @tt{thenWT} are like the
 * @tt{thenT} tactical, except that they apply their second argument
 * only to the goals labeled ``main'', ``equality'', or ``wf'' respectively.
 * @tt{thenAT} applies its second argument only to the goal that @emph{not}
 * labeled ``main''.}
 *
 * @item{@tactic[whileProgressMT], @tactic[untilFailMT], @tactic[repeatMT], @tactic[repeatMForT];
 * These tactics repeat the argument tactic  only
 * on the subgoals labeled ``main''.}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let addHiddenLabelT = Tactic_type.Tacticals.addHiddenLabelT
let removeHiddenLabelT = Tactic_type.Tacticals.removeHiddenLabelT
let keepingLabelT = Tactic_type.Tacticals.keepingLabelT
let ifLabT = Tactic_type.Tacticals.ifLabT
let prefix_thenMT = Tactic_type.Tacticals.prefix_thenMT
let prefix_thenMLT = Tactic_type.Tacticals.prefix_thenMLT
let prefix_thenAT = Tactic_type.Tacticals.prefix_thenAT
let prefix_thenALT = Tactic_type.Tacticals.prefix_thenALT
let prefix_thenWT = Tactic_type.Tacticals.prefix_thenWT
let prefix_thenET = Tactic_type.Tacticals.prefix_thenET
let prefix_thenPT = Tactic_type.Tacticals.prefix_thenPT
let repeatMT = Tactic_type.Tacticals.repeatMT
let untilFailMT = Tactic_type.Tacticals.untilFailMT
let whileProgressMT = Tactic_type.Tacticals.whileProgressMT
let repeatMForT = Tactic_type.Tacticals.repeatMForT
let seqOnMT = Tactic_type.Tacticals.seqOnMT
let completeMT = Tactic_type.Tacticals.completeMT
let labProgressT = Tactic_type.Tacticals.labProgressT

let thinMatchT thinT assum p =
   let goal = Tactic_type.Sequent.goal p in
   let index = Match_seq.match_hyps
      (Refiner.Refiner.TermMan.explode_sequent goal)
      (Refiner.Refiner.TermMan.explode_sequent assum) in
   let rec tac j =
      if j = 0 then idT else
         match index.(pred j) with
            Some _ ->
               tac (pred j)
          | None ->
               thinT j thenT tac (pred j)
   in
      tac (Tactic_type.Sequent.hyp_count p) p

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
