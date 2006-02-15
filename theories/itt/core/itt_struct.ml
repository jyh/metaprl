doc <:doc<
   @spelling{thinned thins}
   @module[Itt_struct]

   The @tt[Itt_struct] module defines @emph{structural} rules.
   Structural rules are logical operations like thinning and substitution
   that are not associated with a particular type.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1997-2006 MetaPRL Group, Cornell University and
   California Institute of Technology

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
   @parents
>>
extends Itt_equal
doc docoff

open Lm_debug
open Lm_printf
open Lm_int_set

open Basic_tactics
open Term_hash_code
open Simple_print

open Itt_equal

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules

   @modsubsection{Structural rules}

   The @tt[thin_many] rule states that if the conclusion <<'C>> can be proved
   from hypotheses defined in <<df_context_var[H]>> and <<df_context_var[K]>>,
   then it can also be proved with additional assumptions <<df_context_var[J]>>.
   The name comes from the goal-directed view: the hypotheses <<df_context_var[J]>>
   are removed (``thinned'') by the application of the rule.

   Note that the rule requires that variables introduced by <<df_context_var[J]>>
   may not occur free in <<df_context_var[K]>> or <<'C>>.

   The proof extract term <<'t>> is unchanged.
>>
prim thin_many 'H 'J :
   ('t : sequent { <H>; <K> >- 'C }) -->
   sequent { <H>; <J>; < K<|H|> > >- 'C<|H;K|> } =
   't

interactive thin 'H :
   sequent { <H>; <J> >- 'C } -->
   sequent { <H>; 'A; <J> >- 'C }

prim exchange 'H 'K 'L:
   ('t : sequent { <H>; <L>; <K>; <J> >- 'C }) -->
   sequent { <H>; <K>; < L<|H|> >; <J> >- 'C } =
   't

doc <:doc<
   @modsubsection{Cut (lemma instantiation)}

   The @tt{cut} rule is an alternate form of @emph{modus-ponens}.
   If the lemma <<'S>> can be proved from the current assumptions <<df_context_var[H]>>
   and <<df_context_var[J]>>, and the goal <<'T>> can be proved with
   this additional assumption, the lemma can be instantiated to obtain a proof of the goal.

   The extract term is formed by instantiating the proof <<'a>> of the lemma
   in the abstracted proof <<'f['x]>>, to get a proof <<'f['a]>> of <<'T>>.
>>
prim cut 'H 'S :
   [assertion] ('a : sequent { <H>; <J> >- 'S }) -->
   [main] ('f['x] : sequent { <H>; x: 'S; <J> >- 'T }) -->
   sequent { <H>; <J> >- 'T } =
   'f['a]

doc docoff

(* This is usually used for performance testing. *)
interactive dup :
   sequent { <H> >- 'T } -->
   sequent { <H> >- 'T } -->
   sequent { <H> >- 'T}

doc <:doc<
   @modsubsection{Explicit proof introduction}

   The @tt{introduction} rule performs proof by explicit introduction
   of a proof term.  If the program $t$ has type $T$, then $T$ is
   provable with proof extract $t$.
>>
prim introduction 't :
   [wf] sequent { <H> >- 't in 'T } -->
   sequent { <H> >- 'T } =
   't

doc <:doc<
   @modsubsection{Axiom}

   The @tt{hypothesis} rule defines proof by assumption: if $A$ is
   assumed, then it is true.
>>

(*
 * H; x: A; J >- A ext x
 * by hypothesis
 *)
interactive hypothesis {| nth_hyp |} 'H :
   sequent { <H>; x: 'A; <J['x]> >- 'A }

interactive hypothesisType {| nth_hyp |} 'H :
   sequent { <H>; x: 'A; <J['x]> >- "type"{'A} }

interactive hypMem {| nth_hyp |} 'H :
   sequent { <H>; x: 't1 = 't2 in 'A; <J['x]> >- 'A }

interactive hypMemType {| nth_hyp |} 'H :
   sequent { <H>; x: 't1 = 't2 in 'A; <J['x]> >- "type"{'A} }

interactive equalitySymHyp {| nth_hyp |} 'H :
   sequent { <H>; e: 'x = 'y in 'T; <J['e]> >- 'y = 'x in 'T }

interactive equalityRefHyp {| nth_hyp |} 'H :
   sequent { <H>; e: 'x = 'y in 'T; <J['e]> >- 'x in 'T }

interactive equalityRefHyp2 {| nth_hyp |} 'H :
   sequent { <H>; e: 'x = 'y in 'T; <J['e]> >- 'y in 'T }

interactive dup_hyp 'H :
   sequent { <H>; x: 'T; <J['x]>; y: 'T >- 'C['x] } -->
   sequent { <H>; x: 'T; <J['x]> >- 'C['x] }

interactive universeType {| nth_hyp |} 'H :
   sequent { <H>; u: 'x in univ[l:l]; <J['u]> >- 'x Type }

doc <:doc<
   @modsubsection{Substitution}

   There are three rules to define substitution.
   The @tt{substitution} rule defines substitution of an arbitrary
   subterm $t_1$ of the conclusion $T_1[t_1]$ with a new term $t_2$.  For the
   substitution to be valid, the terms $t_1$ and $t_2$ must be equal
   in some type $T_2$, the goal $T_1[t_2]$ must be provable, and the
   conclusion $T_1[x]$ must also be @emph{functional} for arbitrary terms
   $x @in T_2$.  Functionality means that the proofs of $T_1[x]$ must be
   equal for all terms $x @in T_2$; the @tt{type} judgment enforces this
   restriction.  This restriction allows the proof extract term
   $t$ to be copied from the proof of $T_1[t_2]$.

   The << bind{x. 'T_1['x]} >> argument specifies the exact location
   of the subterm to be replaced.
>>
prim substitution ('t1 = 't2 in 'T2) bind{x. 'T1['x]} :
   [equality] sequent { <H> >- 't1 = 't2 in 'T2 } -->
   [main] ('t : sequent { <H> >- 'T1['t2] }) -->
   [wf] sequent { <H>; x: 'T2 >- "type"{'T1['x]} } -->
   sequent { <H> >- 'T1['t1] } =
   't

doc <:doc<
   Hypothesis substitution is defined with two rules.  The @tt{hypReplacement}
   performs entire replacement of a hypothesis $A$ with another $B$.  The
   two types must be equal (in some universe).  The proof extract is
   unchanged.

   The @tt{hypSubstitution} rule performs replacement of an arbitrary
   subterm in a hypothesis, in a similar manner to conclusion substitution.
>>
prim hypReplacement 'H 'B univ[i:l] :
   [main] ('t['x] : sequent { <H>; x: 'B; <J['x]> >- 'T['x] }) -->
   [equality] sequent { <H>; x: 'A; <J['x]> >- 'A = 'B<|H|> in univ[i:l] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'T['x] } =
   't['x]

prim hypSubstitution 'H ('t1 = 't2 in 'T2) bind{y. 'A['y]} :
   [equality] sequent { <H>; x: 'A['t1]; <J['x]> >- 't1 = 't2<|H|> in 'T2 } -->
   [main] ('t['x] : sequent { <H>; x: 'A['t2]; <J['x]> >- 'T1['x] }) -->
   [wf] sequent { <H>; x: 'A['t1]; <J['x]>; z: 'T2 >- "type"{'A['z]} } -->
   sequent { <H>; x: 'A['t1]; <J['x]> >- 'T1['x] } =
   't['x]

doc <:doc<
   @modsubsection{Equality in a type}

   Equality in any term $T$ means that $T$ is a type.
>>
interactive equalityTypeIsTypeHyp {| nth_hyp |} 'H :
   sequent { <H>; x: 'a = 'b in 'T; <J['x]> >- "type"{'T} }

interactive equalityTypeIsType 'a 'b :
   [wf] sequent { <H> >- 'a = 'b in 'T } -->
   sequent { <H> >- "type"{'T} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

doc <:doc<
   @tactics
   @modsubsection{Thinning}
   The @tactic[thinT] tactic uses the @hrefrule[thin] rule to
   @emph{thin} a hypothesis in the current goal.

   $$
   @rulebox{thinT; i;
     <<sequent{ <H>; <J> >- 'C}>>;
     <<sequent{ <H>; "i. x": 'A; <J> >- 'C}>>}
   $$

   @noindent
   The @tactic[thinAllT] tactic thins a sequence of hypotheses.

   $$
   @rulebox{thinAllT; i@ j;
      <<sequent{ <H>; <J> >- 'C}>>;
      <<sequent{ <H>; "i. x_i": 'A_i; math_cdots; "j. x_j": 'A_j; <J> >- 'C}>>}
   $$

   We also create a new version of @hreftactic[nthAssumT] tactic that knows how
   to do thinning. This new @tt[nthAssumT] is added to @hreftactic[trivialT].

   @docoff
>>
let thinT = thin

let thinTermT =
   let rec findThinT t hyps i =
      if i = 0 then
         idT
      else
         let i' = i - 1 in
            match SeqHyp.get hyps i' with
               Hypothesis(_, t') when alpha_equal t t' ->
                  thin i
             | _ ->
                  findThinT t hyps i'
   in argfunT (fun t p ->
      let e = explode_sequent_arg p in
      let hyps = e.sequent_hyps in
         findThinT t hyps (SeqHyp.length e.sequent_hyps))

let thinIfThinningT = argfunT (fun hyps p ->
    if get_thinning_arg p then
       tryOnHypsT hyps thinT
    else idT)

let thinAllT i j = funT (fun p ->
   let i = get_pos_hyp_num p i in
   let j = get_pos_hyp_num p j in
      thin_many i (j-i+2) )

(*
 * Thin duplicates.
 *)
let thin_dup p =
   let hyps = (explode_sequent (Sequent.goal p)).sequent_hyps in
   let _, thins =
      SeqHyp.fold (fun (table, thins) i h ->
            match h with
               Hypothesis (_, t) ->
                  let code = hash_term t in
                  let tl =
                     try IntMTable.find_all table code with
                        Not_found ->
                           []
                  in
                     if List.exists (fun t' -> alpha_equal t' t) tl then
                        table, i :: thins
                     else
                        IntMTable.add table code t, thins
             | Context _ ->
                  table, thins) (IntMTable.empty, []) hyps
   in

   (*
    * Note that the hyp numbers in SeqHyp.fold start from 0,
    * but the thinT tactic expects numbers to start from 1.
    *)
   let rec thin_dup thins =
      match thins with
         i :: thins ->
            tryT (thinT (succ i))
            thenT thin_dup thins
       | [] ->
            idT
   in
      thin_dup thins

let thinDupT = funT thin_dup

let nthAssumT = 
   let matchAssumT = Auto_tactic.matchAssumT (cut 0) in
      argfunT (fun i p ->
         let assum = Sequent.nth_assum p i in
            Top_tacticals.thinMatchT thin_many (nth_hyp_mem p) assum thenT matchAssumT i)

doc <:doc<
   @modsubsection{Reordering}
   The @tactic[moveHypT] $i$ $j$ tactic used the @hrefrule[exchange] rule to @emph{move} a hypothesis
   in the current goal from position $i$ to position $j$. For example, when $j>i$,
   $$
   @rulebox{moveHypT; i j;
     <<sequent{ <H>; <J>; "j. x": 'A; <K> >- 'C}>>;
     <<sequent{ <H>; "i. x": 'A; <J>; <K> >- 'C}>>}
   $$
   @docoff
>>
let moveHypT i j = funT (fun p ->
   let i = get_pos_hyp_num p i in
   let j = get_pos_hyp_num p j in
      if j > i then
         exchange i 2 (j - i + 1)
      else
         exchange j (i - j + 1) 2)

doc <:doc<
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
>>
let assertT = cut 0

let dupHypT = dup_hyp

let tryAssertT s ta tm = funT (fun p ->
   if alpha_equal s (Sequent.concl p) then ta else
      assertT s thenLT [ta;tm])

doc <:doc<
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
>>
let assertAtT i s =
   let i = if i < 0 then i + 1 else i in
      cut i s

let copyHypT i j = funT (fun p ->
   assertAtT j (Sequent.nth_hyp p i) thenAT hypothesis i)

let dupT = dup

doc <:doc<
   @modsubsection{Explicit witness introduction}

   The @tactic[useWitnessT] tactic uses the @hrefrule[introduction] rule
   to perform explicit proof witness introduction.

   $$
   @rulebox{useWitnessT; t;
     <<sequent{ <H> >- 't in 'T}>>;
     <<sequent{ <H> >- 'T}>>}
   $$

   @docoff
>>
let useWitnessT = introduction

doc <:doc<
   @modsubsection{Substitution}

   The three substitution rules are unified into a single
   tactic @tactic[substT], which takes a clause number $i$, and
   an equality $t_1 = t_2 @in T$.  The tactic substitutes $t_2$ for
   @emph{all} occurrences of the term $t_1$ in the clause.  The following
   example illustrates the use.

   $$
   @rulebox{substT; (1 + 2 = 3 @in @int)@space@tt[0];
      @ldots @i{equality} @ldots <<sequent{ <H> >- <:doc<1 + 2 = 3 @in @int>>}>>@cr
      @ldots @i{main} @ldots <<sequent{ <H> >- <:doc<3 < 1 * 3>>}>>@cr
      @ldots @i{wf} @ldots <<sequent{ <H>; x: (<:doc<@int>>) >- "type"{<:doc<(x < 1 * x)>>}}>>;
      <<sequent{ <H> >- <:doc< (1 + 2) < 1 * (1 + 2)>>}>>}
   $$

   The @hreftactic[substT] tactic is resource-bases, which will allow adding other
   kinds of equality-based substitutions (such as squiggle substitution) in later theories.

   @docoff
>>

open Term_match_table

let extract_subst tbl t =
   match lookup tbl select_all t with
      Some subst -> subst t
    | None -> raise (RefineError ("Itt_struct.substT", StringTermError("Found nothing appropriate for", t)))

let resource (term * (term -> int -> tactic), term -> int -> tactic) subst =
   table_resource_info extract_subst

let substTaux t i = funT (fun p ->
   Sequent.get_resource_arg p get_subst_resource t i)

let substConclT t = substTaux t 0

let local_substConclT = argfunT (fun t p ->
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
let resource subst +=
   equal_term, (fun t i -> if i = 0 then local_substConclT t else substHypT i t)

let move_and_substT t i = funT (fun p ->
   let i = get_pos_hyp_num p i in
      copyHypT i (-1) thenT substTaux t (-1) thenT tryT (thinT i))

let substT t i =
   if i = 0 then
      substTaux t i
   else
      substTaux t i orelseT move_and_substT t i

let justSubstT t i tac j =
   let t1 = substTaux t i thenET tac j in
      if i = 0 then
         t1
      else
         t1 orelseT funT (fun p ->
            let j = get_pos_hyp_num p j in
              copyHypT i (-1) thenT substTaux t (-1) thenET tac j thenT tryT (thinT i))

(*
 * Derived versions.
 *)
let hypSubstT i j = funT (fun p ->
   justSubstT (Sequent.nth_hyp p i) j hypothesis i)

(*
 * XXX: HACK (2005/12/21 nogin). A "proper" way of doing this is resource-based.
 * However I am hoping that this hack will cover all the interesting cases.
 *)
let rec swap_bterm t = function
   [t'] ->
      let t' = dest_bterm t' in
         [mk_bterm t'.bvars (swap t t'.bterm)]
 | [t1; t2] when is_simple_bterm t1 && is_simple_bterm t2 ->
      [t2; t1]
 | []
 | [_; _] ->
       raise (RefineError("Itt_struct.revHypSubstT", StringTermError("Do not know how to reverse the hyp", t)))
 | hd :: tl ->
       hd :: (swap_bterm t tl)

and swap t_orig t =
   let t = dest_term t in
      mk_term t.term_op (swap_bterm t_orig t.term_terms)

let revHypSubstT i j = funT (fun p ->
   let t = Sequent.nth_hyp p i in
      justSubstT (swap t t) j nthHypT i)

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

doc <:doc<
   @resources

   The (@tt["onSomeAssumT equalityAssumT"]) tactic is added to the @hreftactic[trivialT]
   resource.

   @docoff
>>
let resource auto += {
   auto_name = "Itt_struct.autoAssumT";
   auto_prec = create_auto_prec [equality_prec] [];
   auto_tac = onSomeAssumT nthAssumT;
   auto_type = AutoTrivial;
}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
