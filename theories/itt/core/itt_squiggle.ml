doc <:doc<
   @module[Itt_squiggle]

   The @tt[Itt_squiggle] module defines the squiggle equality.
   The squiggle equality <<'t ~ 's>> holds for closed terms $t$ and $s$ iff
   $t$ can be reduced to $s$. We can expand this semantics for open terms
   in the given context the same way as for any other type.
   For example one can prove that
   $$<<sequent{ <H>; x: <:doc<@prod{A;B}>> >- 'x ~ (<:doc<@pair{@fst{x};@snd{x}}>>)}>>$$
   This is a conditional rewrite: it states that we can replace $x$ with
   $@pair{@fst{x};@snd{x}}$ only when we know that $x$ is from a product type.
   The rules @hrefrule[squiggleSubstitution] and @hrefrule[squiggleHypSubstitution]
   define when such substitution would be valid.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

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

   @end[license]
>>

doc <:doc<
   @parents
>>

extends Itt_equal
extends Itt_struct

doc docoff
extends Itt_comment

open Lm_debug
open Lm_printf

open Base_rewrite
open Basic_tactics

open Itt_equal
open Itt_struct

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*************************************************************************
 * @terms
 * The @tt[sqeq] term defines the squiggle equality.
 *
 *)
(*
declare "sqeq"{'t;'s}
*)

doc docoff

dform sqeq_df : ('a ~ 'b) = szone slot{'a} `" " equiv hspace slot{'b} ezone

let squiggle_term = << 'a ~ 'b >>
let squiggle_opname = opname_of_term squiggle_term
let is_squiggle_term = is_dep0_dep0_term squiggle_opname
let dest_squiggle = dest_dep0_dep0_term squiggle_opname
let mk_squiggle_term = mk_dep0_dep0_term squiggle_opname

doc <:doc<
   @rewrites
   @modsubsection{Typehood and equality}
   The squiggle relation <<'t ~ 's>> is a type if and only if
   it holds.  Two squiggle relation <<'t_1 ~ 's_1>> and <<'t_2 ~ 's_2>>
   are equal as types whenever they are correct types.
>>
prim squiggleEquality {| intro [] |} :
  [wf] sequent{ <H> >- 't1 ~ 's1 } -->
  [wf] sequent{ <H> >- 't2 ~ 's2 } -->
  sequent{ <H> >- ('t1 ~ 's1) = ('t2 ~ 's2) in univ[i:l]} =
  it

interactive squiggleType {| intro [] |} :
  [wf] sequent{ <H> >- 't ~ 's } -->
  sequent{ <H> >- "type"{'t ~ 's}}

doc <:doc<
   @modsubsection{Membership}
   The <<it>> term is the one-and-only element
   in a provable squiggle equality type.
>>

prim squiggleElimination {|  elim [ThinOption thinT] |} 'H :
   ('f['x] : sequent{ <H>; x: ('t ~ 's); <J[it]> >- 'C[it] }) -->
   sequent { <H>; x: ('t ~ 's); <J['x]> >- 'C['x] } =
   'f['x]

interactive squiggle_memberEquality {| intro [] |} :
  [wf] sequent{ <H> >- 't ~ 's } -->
  sequent{ <H> >- it in ('t ~ 's)}

doc <:doc<
   @modsubsection{Squiggle equality is an equivalence relation}
   Squiggle equality is reflexive, symmetric and transitive
   (the symmetry and transitivity rules are proven in the Substitution section below).
>>

prim squiggleRef {|  intro [] |} :
   sequent { <H> >- 't ~ 't } =
   it

doc <:doc<
   @modsubsection{Substitution}
   If we can prove that <<'t ~ 's>>, then we can substitute $s$ for $t$
   in any place without generating any well-formedness subgoals.
>>

prim squiggleHypSubstitution 'H ('t ~ 's) bind{x. 'A['x]}:
   [equality] sequent { <H>; x: 'A['t]; <J['x]> >- 't ~ 's } -->
   [main] ('f['x]: sequent { <H>; x: 'A['s]; <J['x]> >- 'C['x] }) -->
   sequent { <H>; x: 'A['t]; <J['x]> >- 'C['x] } =
   'f['x]

interactive squiggleSubstitution ('t ~ 's) bind{x. 'A['x]} :
   [equality] sequent{ <H> >- 't ~ 's } -->
   [main] sequent{ <H> >- 'A['s] } -->
   sequent { <H> >-  'A['t] }

doc <:doc<
   The  @tt[sqSubstT] tactic takes a clause number $i$, and
   a term <<'t ~ 's>> and applies one of two above rules.
   This tactic substitutes the term $s$ for
   @emph{all} occurrences of the term $t$ in the clause.
   One can give a term  << bind{x. 'A['x]} >> as an optional with-argument
   to specify exact location of the subterm to be replaced.
>>

interactive squiggleSym {| nth_hyp |} :
   sequent { <H> >- 's ~ 't } -->
   sequent { <H> >- 't ~ 's }

interactive squiggleTrans 'r :
   sequent { <H> >- 't ~ 'r } -->
   sequent { <H> >- 'r ~ 's } -->
   sequent { <H> >- 't ~ 's }

doc docoff

interactive squiggleFormation ('t ~ 's) :
  [wf] sequent{ <H> >- 't ~ 's } -->
  sequent{ <H> >- univ[i:l]}
     (* = 't ~ 's *)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(* substitution *)

let sqSubstConclT = argfunT (fun t p ->
   let a, _ = dest_squiggle t in
      squiggleSubstitution t (get_bind_from_arg_or_concl_subst p a))

(*
 * Hyp substitution requires a replacement.
 *)
let sqSubstHypT i t = funT (fun p ->
   let a, _ = dest_squiggle t in
   let i = Sequent.get_pos_hyp_num p i in
   let bind = get_bind_from_arg_or_hyp_subst p i a in
      squiggleHypSubstitution i t bind)

(*
 * General substition.
 *)
let sqSubstT t i =
   if i = 0 then
      sqSubstConclT t
   else
      sqSubstHypT i t

let resource subst +=
   squiggle_term, sqSubstT

let sqSymT = squiggleSym

let revSqTerm trm =
      let a, b = dest_squiggle trm in
        mk_squiggle_term  b a

let hypC i = funC (fun p ->
   let trm = Sequent.nth_hyp (env_arg p) i in
   rewriteC trm thenTC hypothesis i)

let revHypC i = funC (fun p ->
   let trm = Sequent.nth_hyp (env_arg p) i in
   rewriteC (revSqTerm trm) thenTC (sqSymT thenT hypothesis i))

let assumC i = funC (fun p ->
   let trm = TermMan.concl (Sequent.nth_assum (env_arg p) i) in
   rewriteC trm  thenTC nthAssumT i)

let revAssumC i = funC (fun p ->
   let trm = TermMan.concl (Sequent.nth_assum (env_arg p) i) in
   rewriteC (revSqTerm trm)  thenTC (sqSymT thenT nthAssumT i))

