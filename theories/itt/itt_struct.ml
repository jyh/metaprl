(*!
 * @begin[spelling]
 * assertT hypReplacement hypSubstitution nthHypT onSomeHypT
 * ponens substT substition thinAllT thinT thinned
 * thinning thins useWitnessT wf struct
 * @end[spelling]
 *
 * @begin[doc]
 * @theory[Itt_struct]
 *
 * The @tt{Itt_struct} module defines @emph{structural} rules.
 * Structural rules are logical operations like thinning and substitution
 * that are not associated with a particular type.
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
 * Author: Jason Hickey @email{jyh@cs.caltech.edu}
 * Modified by: Aleksey Nogin @email{nogin@cs.cornell.edu}
 *
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Itt_equal
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Var
open Mptop

open Base_auto_tactic

open Itt_equal

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_struct%t"

(* debug_string DebugLoad "Loading itt_struct..." *)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 *
 * @thysubsection{Thinning (of hypotheses)}
 *
 * The @tt{thin} rule states that if the conclusion $C$ can be proved
 * from hypotheses defined in $H$ and $J$, then it can also be proved with
 * an additional assumption $x@colon A$.  The name comes from the
 * goal-directed view: the hypothesis $x@colon A$ is removed (``thinned'')
 * by the application of the rule.
 *
 * Note that $x$ must be a variable that is not bound by any hypothesis
 * in $H$.  The rule is even more stringent: $x$ may not occur free
 * in $J$ or $C$ (note that the goal is @emph{not} phrased as
 * $@sequent{ext; {H; x@colon A; J[x]}; C}$).
 *
 * The proof extract term $t$ is unchanged.
 * @end[doc]
 *)
prim thin 'H 'J :
   ('t : sequent ['ext] { 'H; 'J >- 'C }) -->
   sequent ['ext] { 'H; x: 'A; 'J >- 'C } =
   't

prim exchange 'H 'K 'L 'J:
   ('t : sequent ['ext] { 'H; 'L; 'K; 'J >- 'C }) -->
   sequent ['ext] { 'H; 'K; 'L; 'J >- 'C } =
   't

(*!
 * @begin[doc]
 * @thysubsection{Cut (lemma instantiation)}
 *
 * The @tt{cut} rule is an alternate form of @emph{modus-ponens}.
 * If the lemma $S$ can be proved from the current assumptions $H$
 * and $J$, and the goal $T$ can be proved with this additional assumption,
 * the lemma can be instantiated to obtain a proof of the goal.
 *
 * The extract term is formed by instantiating the proof $a$ of the lemma
 * in the abstracted proof $f[x]$, to get a proof $f[a]$ of $T$.
 * @end[doc]
 *)
prim cut 'H 'J 'S 'x :
   [assertion] ('a : sequent ['ext] { 'H; 'J >- 'S }) -->
   [main] ('f['x] : sequent ['ext] { 'H; x: 'S; 'J >- 'T }) -->
   sequent ['ext] { 'H; 'J >- 'T } =
   'f['a]

(*!
 * @docoff
 *
 * This is usually used for performance testing.
 *)
interactive dup 'H :
   sequent ['ext] { 'H >- 'T } -->
   sequent ['ext] { 'H >- 'T } -->
   sequent ['ext] { 'H >- 'T}

(*!
 * @begin[doc]
 * @thysubsection{Explicit proof introduction}
 *
 * The @tt{introduction} rule performs proof by explicit introduction
 * of a proof term.  If the program $t$ has type $T$, then $T$ is
 * provable with proof extract $t$.
 * @end[doc]
 *)
prim introduction 'H 't :
   [wf] sequent [squash] { 'H >- 't IN 'T } -->
   sequent ['ext] { 'H >- 'T } =
   't

(*!
 * @begin[doc]
 * @thysubsection{Axiom}
 *
 * The @tt{hypothesis} rule defines proof by assumption: if $A$ is
 * assumed, then it is true.  The proof extract term is the program
 * denoted by the assumption $x@colon A$.
 * @end[doc]
 *)

(*
 * H; x: A; J >- A ext x
 * by hypothesis
 *)
interactive hypothesis 'H 'J 'x :
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'A }

(*!
 * @begin[doc]
 * @thysubsection{Substitution}
 *
 * There are three rules to define substitution.
 * The @tt{substitution} rule defines substitution of an arbitrary
 * subterm of the conclusion $T_1[t_1]$ with a new term $t_2$.  For the
 * substitution to be valid, the terms $t_1$ and $t_2$ must be equal
 * in some type $T_2$, the goal $T_1[t_2]$ must be provable, and the
 * conclusion $T_1[x]$ must also be @emph{functional} for arbitrary terms
 * $x @in T_2$.  Functionality means that the proofs of $T_1[x]$ must be
 * equal for all terms $x @in T_2$; the @tt{type} judgment enforces this
 * restriction.  This restriction allows the proof extract term
 * $t$ to be copied from the proof of $T_1[t_2]$.
 *
 * The $<< bind{x. 'T_1['x]} >>$ argument specifies the exact location
 * of the subterm to be replaced.
 * @end[doc]
 *)
prim substitution 'H ('t1 = 't2 in 'T2) bind{x. 'T1['x]} :
   [equality] sequent [squash] { 'H >- 't1 = 't2 in 'T2 } -->
   [main] ('t : sequent ['ext] { 'H >- 'T1['t2] }) -->
   [wf] sequent [squash] { 'H; x: 'T2 >- "type"{'T1['x]} } -->
   sequent ['ext] { 'H >- 'T1['t1] } =
   't

(*!
 * @begin[doc]
 * Hypothesis substition is defined with two rules.  The @tt{hypReplacement}
 * performs entire replacement of a hypothesis $A$ with another $B$.  The
 * two types must be equal (in some universe).  The proof extract is
 * unchanged.
 *
 * The @tt{hypSubstitution} rule performs replacement of an arbitrary
 * subterm in a hypothesis, in a similar manner to conclusion substitution.
 * @end[doc]
 *)
prim hypReplacement 'H 'J 'B univ[i:l] :
   [main] ('t : sequent ['ext] { 'H; x: 'B; 'J['x] >- 'T['x] }) -->
   [equality] sequent [squash] { 'H; x: 'A; 'J['x] >- 'A = 'B in univ[i:l] } -->
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'T['x] } =
   't

prim hypSubstitution 'H 'J ('t1 = 't2 in 'T2) bind{y. 'A['y]} 'z :
   [equality] sequent [squash] { 'H; x: 'A['t1]; 'J['x] >- 't1 = 't2 in 'T2 } -->
   [main] ('t : sequent ['ext] { 'H; x: 'A['t2]; 'J['x] >- 'T1['x] }) -->
   [wf] sequent [squash] { 'H; x: 'A['t1]; 'J['x]; z: 'T2 >- "type"{'A['z]} } -->
   sequent ['ext] { 'H; x: 'A['t1]; 'J['x] >- 'T1['x] } =
   't

(*!************************************************************************
 * @begin[doc]
 * @thysubsection{Equality in a type}
 *
 * Equality in any term $T$ means that $T$ is a type.
 * @end[doc]
 *)
interactive equalityTypeIsType 'H 'a 'b :
   [wf] sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- "type"{'T} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*!
 * @begin[doc]
 * @tactics
 *
 * @thysubsection{Axiom}
 * The @tactic[nthHypT] tactic uses the @hrefrule[hypothesis] rule
 * to perform proof by assumption.
 *
 * $$
 * @rulebox{nthHypT; i;
 *    @cdot;
 *    @sequent{ext; {H; i@colon x@colon A; J}; A}}
 * $$
 *
 * @docoff
 * @end[doc]
 *)
let nthHypT i p =
   let x, h = Sequent.nth_hyp p i in
   let i, j = Sequent.hyp_indices p i in
      hypothesis i j x p

(*!
 * @begin[doc]
 * @thysubsection{Thinning}
 * The @tactic[thinT] tactic uses the @hrefrule[thin] rule to
 * @emph{thin} a hypothesis in the current goal.
 *
 * $$
 * @rulebox{thinT; i;
 *   @sequent{ext; {H; J}; C};
 *   @sequent{ext; {H; i@colon x@colon A; J}; C}}
 * $$
 *
 * @noindent
 * The @tactic[thinAllT] tactic thins a sequence of hypothesis.
 *
 * $$
 * @rulebox{thinAllT; i@ j;
 *    @sequent{ext; {H; J}; C};
 *    @sequent{ext; {H; i@colon x_i@colon A_i; @cdots; j@colon x_j@colon A_j; J}; C}}
 * $$
 *
 * @docoff
 * @end[doc]
 *)
let thinT i p =
   let i, j = Sequent.hyp_indices p i in
      thin i j p

let thinMatchT assum p =
   let goal = Sequent.goal p in
   let index = Match_seq.match_hyps (explode_sequent goal) (explode_sequent assum) in
   let rec tac j =
      if j = 0 then idT else
         match index.(pred j) with
            Some _ ->
               tac (pred j)
          | None ->
               thinT j thenT tac (pred j)
   in
      tac (Sequent.hyp_count p) p

let thinAllT i j p =
   let rec tac j =
      if j < i then
         idT
      else
         thinT j thenT tac (pred j)
   in
      tac j p

(*!
 * @begin[doc]
 * @thysubsection{Lemma assertion}
 *
 * The @tactic[assertT] tactic uses the @hrefrule[cut] rule to
 * introduce a lemma.
 *
 * $$
 * @rulebox{assertT; A;
 *   @ldots @i{assertion} @ldots @sequent{ext; H; A}@cr
 *     @sequent{ext; {H; x@colon A}; C};
 *   @sequent{ext; H; C}}
 * $$
 *
 * @docoff
 * @end[doc]
 *)
let assertT s p =
   let j, k = Sequent.hyp_split_addr p (Sequent.hyp_count p) in
   let v = maybe_new_vars1 p "v" in
      cut j k s v p

let tryAssertT s ta tm p =
   let concl = Sequent.concl p in
   if alpha_equal s concl then ta p else
      (assertT s thenLT [ta;tm]) p

(*!
 * @begin[doc]
 * @noindent
 * The @tactic[assertAtT] introduces the lemma at a specific
 * location in the hypothesis list.
 *
 * $$
 * @rulebox{assertAtT; i@space A;
 *    @ldots  @i{assertion} @ldots @sequent{ext; {H; J}; A}@cr
 *       @sequent{ext; {H; x@colon A; J}; C};
 *    @sequent{ext; {H; (@i{location}@space i); J}; C}}
 * $$
 *
 * @docoff
 * @end[doc]
 *)
let assertAtT i s p =
   let i, j = Sequent.hyp_split_addr p i in
   let v = get_opt_var_arg "v" p in
      cut i j s v p

let dupT p =
   dup (Sequent.hyp_count_addr p) p

(*!
 * @begin[doc]
 * @thysubsection{Explicit witness introduction}
 *
 * The @tactic[useWitnessT] tactic uses the @hrefrule[introduction] rule
 * to perform explicit proof witness introduction.
 *
 * $$
 * @rulebox{useWitnessT; t;
 *   @sequent{squash; H; t @in T};
 *   @sequent{ext; H; T}}
 * $$
 *
 * @docoff
 * @end[doc]
 *)
let useWitnessT t p =
   introduction (Sequent.hyp_count_addr p) t p

(*!
 * @begin[doc]
 * @thysubsection{Substitution}
 *
 * The three substitution rules are unified into a single
 * tactic @tactic[substT], which takes a clause number $i$, and
 * an equality $t_1 = t_2 @in T$.  The tactic substitutes $t_2$ for
 * @emph{all} occurrences of the term $t_1$ in the clause.  The following
 * example illustrates the use.
 *
 * $$
 * @rulebox{substT; 1 + 2 = 3 @in @int;
 *    @ldots @i{equality} @ldots @sequent{squash; H; 1 + 2 = 3 @in @int}@cr
 *    @ldots @i{main} @ldots @sequent{ext; H; 3 < 1 * 3}@cr
 *    @ldots @i{wf} @ldots @sequent{squash; {H; i@colon @int}; @type{(x < 1 * x)}};
 *    @sequent{ext; H; (1 + 2) < 1 * (1 + 2)}}
 * $$
 *
 * @docoff
 * @end[doc]
 *)
let substConclT t p =
   let _, a, _ = dest_equal t in
   let bind =
      try
         let t1 = get_with_arg p in
            if is_xbind_term t1 then
               t1
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", t)))
      with
         RefineError _ ->
            let x = get_opt_var_arg "z" p in
               mk_xbind_term x (var_subst (Sequent.concl p) a x)
   in
      substitution (Sequent.hyp_count_addr p) t bind p

(*
 * Hyp substitution requires a replacement.
 *)
let substHypT i t p =
   let _, a, _ = dest_equal t in
   let _, t1 = Sequent.nth_hyp p i in
   let z = get_opt_var_arg "z" p in
   let bind =
      try
         let b = get_with_arg p in
            if is_xbind_term b then
               b
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", b)))
      with
         RefineError _ ->
            mk_xbind_term z (var_subst t1 a z)
   in
   let i, j = Sequent.hyp_indices p i in
      hypSubstitution i j t bind z p

(*
 * General substition.
 *)
let substT t i =
   if i = 0 then
      substConclT t
   else
      substHypT i t

(*
 * Derived versions.
 *)
let hypSubstT i j p =
   let _, h = Sequent.nth_hyp p i in
      (substT h j thenET nthHypT i) p

let revHypSubstT i j p =
   let t, a, b = dest_equal (snd (Sequent.nth_hyp p i)) in
   let h' = mk_equal_term t b a in
      (substT h' j thenET (equalSymT thenT nthHypT i)) p

(*
 * Replace the entire hypothesis.
 *)
let replaceHypT t i p =
   let j, k = Sequent.hyp_indices p i in
   let univ = get_univ_arg p in
      hypReplacement j k t univ p

(*!
 * @begin[doc]
 * @resources
 *
 * The (@tt{onSomeHypT nthHypT}) tactic is added to the @hreftactic[trivialT]
 * resource.
 *
 * @docoff
 * @end[doc]
 *)
let resource trivial += {
   auto_name = "nthHypT";
   auto_prec = trivial_prec;
   auto_tac = onSomeHypT nthHypT
}

(*
 * Typehood from equality.
 *)
let equalTypeT a b p =
   equalityTypeIsType (Sequent.hyp_count_addr p) a b p

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
