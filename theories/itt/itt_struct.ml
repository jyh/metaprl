doc <:doc< 
   @begin[spelling]
   assertT hypReplacement hypSubstitution nthHypT onSomeHypT
   ponens substT substition thinAllT thinT thinned
   thinning thins useWitnessT wf struct assertAtT
   @end[spelling]
  
   @begin[doc]
   @module[Itt_struct]
  
   The @tt{Itt_struct} module defines @emph{structural} rules.
   Structural rules are logical operations like thinning and substitution
   that are not associated with a particular type.
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
  
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.
  
   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.
  
   Copyright (C) 1998 Jason Hickey, Cornell University
  
   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.
  
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
  
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
  
   Author: Jason Hickey @email{jyh@cs.caltech.edu}
   Modified by: Aleksey Nogin @email{nogin@cs.cornell.edu}
  
   @end[license]
>>

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_equal
doc <:doc< @docoff >>

open Printf
open Lm_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Sequent
open Tactic_type.Tacticals
open Var
open Mptop

open Auto_tactic

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

doc <:doc< 
   @begin[doc]
   @rules
  
   @modsubsection{Thinning (of hypotheses)}
  
   The @tt{thin} rule states that if the conclusion $C$ can be proved
   from hypotheses defined in $H$ and $J$, then it can also be proved with
   an additional assumption $x@colon A$.  The name comes from the
   goal-directed view: the hypothesis $x@colon A$ is removed (``thinned'')
   by the application of the rule.
  
   Note that $x$ must be a variable that is not bound by any hypothesis
   in $H$.  The rule is even more stringent: $x$ may not occur free
   in $J$ or $C$ (note that the goal is @emph{not} phrased as
   <<sequent{ <H>; x: 'A; <J['x]> >- 'C}>>).
  
   The proof extract term $t$ is unchanged.
   @end[doc]
>>
prim thin 'H :
   ('t : sequent { <H>; <J> >- 'C }) -->
   sequent { <H>; 'A; <J> >- 'C } =
   't

prim exchange 'H 'K 'L:
   ('t : sequent { <H>; <L>; <K>; <J> >- 'C }) -->
   sequent { <H>; <K>; <L>; <J> >- 'C } =
   't

doc <:doc< 
   @begin[doc]
   @modsubsection{Cut (lemma instantiation)}
  
   The @tt{cut} rule is an alternate form of @emph{modus-ponens}.
   If the lemma $S$ can be proved from the current assumptions $H$
   and $J$, and the goal $T$ can be proved with this additional assumption,
   the lemma can be instantiated to obtain a proof of the goal.
  
   The extract term is formed by instantiating the proof $a$ of the lemma
   in the abstracted proof $f[x]$, to get a proof $f[a]$ of $T$.
   @end[doc]
>>
prim cut 'H 'S :
   [assertion] ('a : sequent { <H>; <J> >- 'S }) -->
   [main] ('f['x] : sequent { <H>; x: 'S; <J> >- 'T }) -->
   sequent { <H>; <J> >- 'T } =
   'f['a]

doc <:doc< 
   @docoff
  
   This is usually used for performance testing.
>>
interactive dup :
   sequent { <H> >- 'T } -->
   sequent { <H> >- 'T } -->
   sequent { <H> >- 'T}

doc <:doc< 
   @begin[doc]
   @modsubsection{Explicit proof introduction}
  
   The @tt{introduction} rule performs proof by explicit introduction
   of a proof term.  If the program $t$ has type $T$, then $T$ is
   provable with proof extract $t$.
   @end[doc]
>>
prim introduction 't :
   [wf] sequent { <H> >- 't in 'T } -->
   sequent { <H> >- 'T } =
   't

doc <:doc< 
   @begin[doc]
   @modsubsection{Axiom}
  
   The @tt{hypothesis} rule defines proof by assumption: if $A$ is
   assumed, then it is true.  The proof extract term is the program
   denoted by the assumption $x@colon A$.
   @end[doc]
>>

(*
 * H; x: A; J >- A ext x
 * by hypothesis
 *)
interactive hypothesis 'H :
   sequent { <H>; x: 'A; <J['x]> >- 'A }

interactive hypothesisType 'H :
   sequent { <H>; x: 'A; <J['x]> >- "type"{'A} }

interactive hypMem 'H :
   sequent { <H>; x: 't1 = 't2 in 'A; <J['x]> >- 'A }

doc <:doc< 
   @begin[doc]
   @modsubsection{Substitution}
  
   There are three rules to define substitution.
   The @tt{substitution} rule defines substitution of an arbitrary
   subterm of the conclusion $T_1[t_1]$ with a new term $t_2$.  For the
   substitution to be valid, the terms $t_1$ and $t_2$ must be equal
   in some type $T_2$, the goal $T_1[t_2]$ must be provable, and the
   conclusion $T_1[x]$ must also be @emph{functional} for arbitrary terms
   $x @in T_2$.  Functionality means that the proofs of $T_1[x]$ must be
   equal for all terms $x @in T_2$; the @tt{type} judgment enforces this
   restriction.  This restriction allows the proof extract term
   $t$ to be copied from the proof of $T_1[t_2]$.
  
   The << bind{x. 'T_1['x]} >> argument specifies the exact location
   of the subterm to be replaced.
   @end[doc]
>>
prim substitution ('t1 = 't2 in 'T2) bind{x. 'T1['x]} :
   [equality] sequent { <H> >- 't1 = 't2 in 'T2 } -->
   [main] ('t : sequent { <H> >- 'T1['t2] }) -->
   [wf] sequent { <H>; x: 'T2 >- "type"{'T1['x]} } -->
   sequent { <H> >- 'T1['t1] } =
   't

doc <:doc< 
   @begin[doc]
   Hypothesis substition is defined with two rules.  The @tt{hypReplacement}
   performs entire replacement of a hypothesis $A$ with another $B$.  The
   two types must be equal (in some universe).  The proof extract is
   unchanged.
  
   The @tt{hypSubstitution} rule performs replacement of an arbitrary
   subterm in a hypothesis, in a similar manner to conclusion substitution.
   @end[doc]
>>
prim hypReplacement 'H 'B univ[i:l] :
   [main] ('t['x] : sequent { <H>; x: 'B; <J['x]> >- 'T['x] }) -->
   [equality] sequent { <H>; x: 'A; <J['x]> >- 'A = 'B in univ[i:l] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'T['x] } =
   't['x]

prim hypSubstitution 'H ('t1 = 't2 in 'T2) bind{y. 'A['y]} :
   [equality] sequent { <H>; x: 'A['t1]; <J['x]> >- 't1 = 't2 in 'T2 } -->
   [main] ('t['x] : sequent { <H>; x: 'A['t2]; <J['x]> >- 'T1['x] }) -->
   [wf] sequent { <H>; x: 'A['t1]; <J['x]>; z: 'T2 >- "type"{'A['z]} } -->
   sequent { <H>; x: 'A['t1]; <J['x]> >- 'T1['x] } =
   't['x]

doc <:doc< ************************************************************************
   @begin[doc]
   @modsubsection{Equality in a type}
  
   Equality in any term $T$ means that $T$ is a type.
   @end[doc]
>>
interactive equalityTypeIsType 'a 'b :
   [wf] sequent { <H> >- 'a = 'b in 'T } -->
   sequent { <H> >- "type"{'T} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @tactics
  
   @modsubsection{Axiom}
   The @tactic[nthHypT] tactic uses the @hrefrule[hypothesis] rule
   to perform proof by assumption.
  
   $$
   @rulebox{nthHypT; i;
      @cdot;
      <<sequent{ <H>; "i. x": 'A; <J> >- 'A}>>}
   $$
  
   @docoff
   @end[doc]
>>
let nthHypT = argfunT (fun i p ->
   let concl = Sequent.concl p in
   let hyp = Sequent.nth_hyp p i in
      if alpha_equal hyp concl then hypothesis i
      else if is_type_term concl then hypothesisType i
      else hypMem i)

doc <:doc< 
   @begin[doc]
   @modsubsection{Thinning}
   The @tactic[thinT] tactic uses the @hrefrule[thin] rule to
   @emph{thin} a hypothesis in the current goal.
  
   $$
   @rulebox{thinT; i;
     <<sequent{ <H>; <J> >- 'C}>>;
     <<sequent{ <H>; "i. x": 'A; <J> >- 'C}>>}
   $$
  
   @noindent
   The @tactic[thinAllT] tactic thins a sequence of hypothesis.
  
   $$
   @rulebox{thinAllT; i@ j;
      <<sequent{ <H>; <J> >- 'C}>>;
      <<sequent{ <H>; "i. x_i": 'A_i; math_cdots; "j. x_j": 'A_j; <J> >- 'C}>>}
   $$

   We also create a new version of @hreftactic[nthAssumT] tactic that knows how
   to do thinning. This new @tt[nthAssumT] is added to @hreftactic[trivialT].
  
   @docoff
   @end[doc]
>>
let thinT = thin

let thinIfThinningT = argfunT (fun hyps p ->
    if get_thinning_arg p then
       tryOnHypsT hyps thinT
    else idT)

let thinAllT i j = funT (fun p ->
   let i = get_pos_hyp_num p i in
   let j = get_pos_hyp_num p j in
   let rec tac j =
      if j < i then
         idT
      else
         thinT j thenT tac (pred j)
   in
      tac j)

let nthAssumT = argfunT (fun i p ->
   let assum = Sequent.nth_assum p i in
      Top_tacticals.thinMatchT thinT assum thenT nthAssumT i)

doc <:doc< 
   @begin[doc]
   @modsubsection{Lemma assertion}
  
   The @tactic[assertT] tactic uses the @hrefrule[cut] rule to
   introduce a lemma.
  
   $$
   @rulebox{assertT; A;
     @ldots @i{assertion} @ldots <<sequent{ <H> >- 'A}>>@cr
       <<sequent{ <H>; x: 'A >- 'C}>>;
     <<sequent{ <H> >- 'C}>>}
   $$
  
   @docoff
   @end[doc]
>>
let assertT = cut 0

let tryAssertT s ta tm = funT (fun p ->
   if alpha_equal s (Sequent.concl p) then ta else
      assertT s thenLT [ta;tm])

doc <:doc< 
   @begin[doc]
   @noindent
   The @tactic[assertAtT] introduces the lemma at a specific
   location in the hypothesis list.
  
   $$
   @rulebox{assertAtT; i@space A;
      @ldots  @i{assertion} @ldots <<sequent{ <H>; <J> >- 'A}>>@cr
         <<sequent{ <H>; x: 'A; <J> >- 'C}>>;
      <<sequent{ <H>; (<:doc<(@i{location}@space i)>>) ; <J> >- 'C}>>}
   $$
  
   @docoff
   @end[doc]
>>
let assertAtT i s =
   let i = if i < 0 then i + 1 else i in
      cut i s

let copyHypT i j = funT (fun p ->
   assertAtT j (Sequent.nth_hyp p i) thenLT [nthHypT i; idT])

let dupT = dup

doc <:doc< 
   @begin[doc]
   @modsubsection{Explicit witness introduction}
  
   The @tactic[useWitnessT] tactic uses the @hrefrule[introduction] rule
   to perform explicit proof witness introduction.
  
   $$
   @rulebox{useWitnessT; t;
     <<sequent{ <H> >- 't in 'T}>>;
     <<sequent{ <H> >- 'T}>>}
   $$
  
   @docoff
   @end[doc]
>>
let useWitnessT = introduction

doc <:doc< 
   @begin[doc]
   @modsubsection{Substitution}
  
   The three substitution rules are unified into a single
   tactic @tactic[substT], which takes a clause number $i$, and
   an equality $t_1 = t_2 @in T$.  The tactic substitutes $t_2$ for
   @emph{all} occurrences of the term $t_1$ in the clause.  The following
   example illustrates the use.
  
   $$
   @rulebox{substT; 1 + 2 = 3 @in @int;
      @ldots @i{equality} @ldots <<sequent{ <H> >- <:doc<1 + 2 = 3 @in @int>>}>>@cr
      @ldots @i{main} @ldots <<sequent{ <H> >- <:doc<3 < 1 * 3>>}>>@cr
      @ldots @i{wf} @ldots <<sequent{ <H>; i: (<:doc<@int>>) >- "type"{.<:doc<(x < 1 * x)>>}}>>;
      <<sequent{ <H> >- <:doc< (1 + 2) < 1 * (1 + 2)>>}>>}
   $$
  
   @docoff
   @end[doc]
>>
let substConclT = argfunT (fun t p ->
   let _, a, _ = dest_equal t in
   let bind = get_bind_from_arg_or_concl_subst p a in
      substitution t bind)

(*
 * Hyp substitution requires a replacement.
 *)
let substHypT i t = funT (fun p ->
   let i = Sequent.get_pos_hyp_num p i in
   let _, a, _ = dest_equal t in
   let bind = get_bind_from_arg_or_hyp_subst p i a in
      hypSubstitution i t bind)

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
let hypSubstT i j = funT (fun p ->
   substT (Sequent.nth_hyp p i) j thenET nthHypT i)

let revHypSubstT i j = funT (fun p ->
   let t, a, b = dest_equal (Sequent.nth_hyp p i) in
   let h' = mk_equal_term t b a in
      substT h' j thenET (equalSymT thenT nthHypT i))

(*
 * Replace the entire hypothesis.
 *)
let replaceHypT t i = funT (fun p ->
   hypReplacement i t (get_univ_arg p))

(*
 * Typehood from equality.
 *)
let equalTypeT = equalityTypeIsType
let memberTypeT a = equalTypeT a a ttca

let equalityAssumT = argfunT (fun i p ->
   let t' = dest_type_term (Sequent.concl p) in
   let t,a,b = dest_equal (TermMan.nth_concl (Sequent.nth_assum p i) 1) in
      if alpha_equal t t' then
         equalTypeT a b thenT nthAssumT i else failT)

let autoAssumT i =
   nthAssumT i orelseT equalityAssumT i

doc <:doc< 
   @begin[doc]
   @resources
  
   The (@tt{onSomeHypT nthHypT}) tactic is added to the @hreftactic[trivialT]
   resource.
  
   @docoff
   @end[doc]
>>
let resource auto += [{
   auto_name = "nthHypT";
   auto_prec = trivial_prec;
   auto_tac = onSomeHypT nthHypT;
   auto_type = AutoTrivial;
}; {
   auto_name = "Itt_struct.autoAssumT";
   auto_prec = create_auto_prec [equality_prec] [];
   auto_tac = onSomeAssumT autoAssumT;
   auto_type = AutoTrivial;
}]

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
