doc <:doc<
   @begin[spelling]
   struct th
   @end[spelling]

   @begin[doc]
   @module[Itt_struct2]

   The @tt{Itt_struct2} module contains some @emph{derived} rules similar
   to @hrefrule[cut] and @hrefrule[substitution] in the @hrefmodule[Itt_struct] theory.
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

   Author: Alexei Kopylov
   @email{kopylov@cs.caltech.edu}

   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_equal
extends Itt_struct
extends Itt_squiggle
extends Itt_squash
extends Itt_set
extends Itt_logic
doc <:doc< @docoff >>

open Lm_debug
open Lm_symbol
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Tacticals
open Top_tacticals
open Var

open Auto_tactic
open Dtactic

open Itt_equal
open Itt_struct
open Itt_squiggle

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_struct2%t"

(* debug_string DebugLoad "Loading itt_struct2..." *)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rules
   @modsubsection{Substitution}

   Using @hrefterm[set] type we can derive more stronger version of the @hrefrule[substitution]
   and @hrefrule[hypSubstitution] rules.
   Suppose we have that $t_1=t_2 @in T$.
   To prove that the substitution $A[t_2]$ for $A[t_1]$ is valid it is necessary to prove that
   the type $A$ is
   functional only for such $x$ @emph{that equals to $t_1$ and $t_2$ in $T$} (not @emph{for all} $x$ as in
   original substitution rules).
   @end[doc]
>>

interactive substitution2 ('t1 = 't2 in 'T) bind{x. 'C['x]} :
   [equality] sequent { <H> >- 't1 = 't2 in 'T } -->
   [main]  sequent { <H> >- 'C['t2] } -->
   [wf] sequent { <H>; x: 'T; v: 't1='x in 'T; w: 't2='x in 'T
                           >- "type"{'C['x]} } -->
   sequent { <H> >- 'C['t1] }

interactive hypSubstitution2 'H ('t1 = 't2 in 'T) bind{y. 'A['y]} :
   [equality] sequent { <H>; x: 'A['t1]; <J['x]> >- 't1 = 't2<|H|> in 'T } -->
   [main] sequent { <H>; x: 'A['t2]; <J['x]> >- 'C['x] } -->
   [wf] sequent { <H>; x: 'A['t1]; <J['x]>; z: 'T; v: 't1='z in 'T; w: 't2<|H|> = 'z in 'T
                           >- "type"{'A['z]} } -->
   sequent { <H>; x: 'A['t1]; <J['x]> >- 'C['x] }

doc <:doc<
   @begin[doc]

   The @tt{Itt_struct2} module redefines tactic @hreftactic[substT].
   From now @tt[substT] uses the above version of substitution
   instead of original one.

   @end[doc]
>>

doc <:doc<
   @begin[doc]
   @modsubsection{Cut rules}

   There are three advanced versions of the @hrefrule[cut] rule.
   The @tt[cutMem] states that if $s @in S$,
   and $T[x]$ is true for any $x$ from $S$ such that $x=s @in S$,
   then $T[s]$ is certainly true.

   @end[doc]
>>

interactive cutMem 's 'S bind{x.'T['x]} :
  [assertion] sequent{ <H> >- 's in 'S } -->
   [main]      sequent { <H>; x: 'S; v: 'x='s in 'S >- 'T['x] } -->
   sequent { <H> >- 'T['s]}

doc <:doc<
   @begin[doc]
   The corresponding tactic is the @tt[letT] tactic.
   This tactic takes a term $x=s @in S$ as an argument
   and a term <<bind{x.'T['x]}>> as an optional with-argument.
   If this argument is omitted then the tactic finds all occurrences of $s$
   in the conclusion and replace them with $x$.

   This tactic is usually used when we have an assumption $s @in S$,
   and want to use the elimination rule corresponding to $S$.

   @end[doc]
>>

(*
interactive cutEqWeak ('s_1='s_2 in 'S) bind{x.'t['x]} 'v 'u :
   [assertion] sequent{ <H> >- 's_1='s_2 in 'S } -->
   [main]      sequent { <H>; x: 'S; v: 's_1='x in 'S; u: 's_2='x in 'S >- 't['x] in 'T } -->
   sequent { <H> >- 't['s_1] = 't['s_2] in 'T}
*)

interactive cutEq0 ('s_1='s_2 in 'S) bind{x.'t_1['x]  't_2['x]} :
   [assertion] sequent{ <H> >- 's_1='s_2 in 'S } -->
   [main]      sequent { <H>; x: 'S; v: 's_1='x in 'S; u: 's_2='x in 'S >- 't_1['x] = 't_2['x] in 'T } -->
   sequent { <H> >- 't_1['s_1] = 't_2['s_2] in 'T}

doc <:doc<
   @begin[doc]
   @modsubsection{Substitution in a type}

   @end[doc]
>>

interactive substitutionInType ('t_1 = 't_2 in 'T) bind{x. 'c_1='c_2 in 'C['x]} :
   [equality] sequent { <H> >- 't_1 = 't_2 in 'T } -->
   [main]  sequent { <H> >-  'c_1 = 'c_2 in 'C['t_2] } -->
   [wf] sequent { <H>; x: 'T; v: 't_1='x in 'T; w: 't_2='x in 'T
                           >- "type"{'C['x]} } -->
   sequent { <H> >- 'c_1 = 'c_2 in 'C['t_1] }

doc <:doc<
   @begin[doc]

   The sequent <<sequent{ <H>; x: 'S; <J['x]> >- 't['x] in 'T}>>
   actually means not only that <<'t['x] in 'T>> for any <<'x in 'S>>, but also
   it means @emph{functionality}, i.e. for any two equal elements $s_1$, $s_2$ of $S$
   $t[s_1]$ and $t[s_2]$ should be equal in $T$.

   The following rule states this explicitly.
   @end[doc]
>>

interactive cutEq ('s_1='s_2 in 'S) bind{x.'t_1['x] = 't_2['x] in 'T['x] } :
   [assertion] sequent{ <H> >- 's_1='s_2 in 'S } -->
   [main]      sequent { <H>; x: 'S; v: 's_1='x in 'S; u: 's_2='x in 'S >- 't_1['x] = 't_2['x] in 'T['x] } -->
   sequent { <H> >- 't_1['s_1] = 't_2['s_2] in 'T['s_1]}

doc <:doc<
   @begin[doc]
   Elimination rule for set equality
   @end[doc]
>>
interactive setEqualityElim {| elim [] |} 'H :
   sequent { <H>; 'a = 'b in 'A; squash{'B['a]}; squash{'B['b]}; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: 'a = 'b in { y: 'A | 'B['y] }; <J['x]> >- 'C['x] }

doc <:doc<
   @begin[doc]

   The @tt[assertEqT] tactic applies this rule.
   This tactic takes a term $s1=s2 @in S$ as an argument
   and a term <<bind{x.'t['x]}>> as an optional with-argument.
   This tactic helps us to prove an equality from a membership.

   @end[doc]
>>

doc <:doc<
   @begin[doc]

   The @tt[cutSquash] rule is similar to the @hrefrule[cut] rule.
   If we prove $S$, but do not show the extract term, then we can assert
   $S$ as a @emph{squashed} hypothesis, that is we are not allow to use its extract
   (see @hrefmodule[Itt_squash]).
   @end[doc]
>>

interactive cutSquash 'H 'S :
   [assertion] sequent { <H>; <J> >- 'S } -->
   [main]      sequent { <H>; x: squash{'S}; <J> >- 'T } -->
   sequent { <H>; <J> >- 'T}

doc <:doc<
   @begin[doc]
   There are two tactics that used this rule: @tt[assertSquashT] and
   @tt[assertSquashAtT].
   They are similar to @hreftactic[assertT] and  @hreftactic[assertAtT].
   The @tt[assertSquashAtT] $n$ $S$ introduces the lemma $S$ after $n$th hypothesis.
   The @tt[assertSquashT] $S$ introduces the lemma $S$ at the end
   of the hypothesis list.

   @docoff
   @end[doc]
>>

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(* substitution *)

let substConclT = argfunT (fun t p ->
   let _, a, _ = dest_equal t in
   let bind = get_bind_from_arg_or_concl_subst p a in
      (substitutionInType t bind orelseT substitution2 t bind) thenWT thinIfThinningT [-1;-1])

(*
 * Hyp substitution requires a replacement.
 *)
let substHypT i t = funT (fun p ->
   let i = Sequent.get_pos_hyp_num p i in
   let _, a, _ = dest_equal t in
   let bind = get_bind_from_arg_or_hyp_subst p i a in
     if get_thinning_arg p
       then hypSubstitution i t bind
       else hypSubstitution2 i t bind)

(*
 * General substition.
 *)

let eqSubstT t i =
   if i = 0 then
      substConclT t
   else
      substHypT i t

let substT t =
   if is_squiggle_term t then
      sqSubstT t
   else
      eqSubstT t

(*
 * Derived versions.
 *)

let hypSubstT i j = funT (fun p ->
   substT (Sequent.nth_hyp p i) j thenET hypothesis i)

let revHypSubstT i j = funT (fun p ->
   let trm = Sequent.nth_hyp p i in
   if is_squiggle_term trm then
      let a, b = dest_squiggle trm in
      let h' = mk_squiggle_term  b a in
         substT h' j thenET (sqSymT thenT hypothesis i)
   else
      let t, a, b = dest_equal trm in
      let h' = mk_equal_term t b a in
         substT h' j thenET (equalSymT thenT hypothesis i))

(* cutMem *)

let letT x_is_s_in_S = funT (fun p ->
   let _S, x, s = dest_equal x_is_s_in_S in
   let xname = dest_var x in
   let bind = get_bind_from_arg_or_concl_subst p s in
      cutMem s  _S bind thenMT nameHypT (-2) (string_of_symbol xname) thenMT thinIfThinningT [-1])

let genT s_in_S = funT (fun p ->
   let _S, _, s = dest_equal s_in_S in
   let bind = get_bind_from_arg_or_concl_subst p s in
      cutMem s  _S bind thenMT thinIfThinningT [-1])

(* cutEq *)

let assertEqT = argfunT (fun eq p ->
   let _, s1, s2 = dest_equal eq in
   let bind =
      try
         get_with_arg p
      with
         RefineError _ ->
            let x = maybe_new_var_arg p (Lm_symbol.add "z") in
            let t, t1,  t2 = dest_equal (Sequent.concl p) in
            let t' = var_subst t s1 x in
            let t1' = var_subst t1 s1 x in
            let t2' = var_subst t2 s2 x in
               <:con< bind{$x$. $mk_equal_term t' t1' t2'$} >>
   in
      if is_xbind_term bind then
         cutEq eq bind thenMT thinIfThinningT [-2;-1]
      else
         raise (RefineError ("assertEqT", StringTermError ("need a \"bind\" term: ", bind))))

(* cutSquash *)

let assertSquashT = cutSquash 0
let assertSquashAtT = cutSquash
