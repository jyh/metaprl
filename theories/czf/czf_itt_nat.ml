doc <:doc<
   @begin[doc]
   @module[Czf_itt_nat]

   The @tt[Czf_itt_nat] module defines the infinite set $@inf$.
   We use the definition of $@inf$ as the definition of the
   natural numbers.  The @tt{zero} term represents the zero,
   and the @tt{succ} term $@succ{i}$ represents $i + 1$.
   The construction is the usual ordinal construction.

   $$
   @begin[array, lcl]
   @line{@zero @equiv @empty}
   @line{@succ{@zero} @equiv @union{@zero; @sing{@zero}}}
   @line{nil @vdots nil}
   @line{@succ{i} @equiv @union{i; @sing{i}}}
   @end[array]
   $$

   The definition of the $@inf$ set uses the @hrefterm[list]
   type as an index type, and it codes the elements using
   the list induction combinator.

   $$@inf @equiv @collect{l; @list{@unit}; @listind{l; @zero; h; t; g; @succ{g}}}$$

   We also define the usual ordering $@lt{i; j}$ on numbers (this
   is just a membership judgment).
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

   Author: Jason Hickey
   @email{jyh@cs.cornell.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Czf_itt_member
extends Czf_itt_singleton
extends Czf_itt_union
extends Czf_itt_empty
extends Czf_itt_implies
doc <:doc< @docoff >>

open Tactic_type
open Tactic_type.Conversionals
open Tactic_type.Tacticals
open Var

open Dtactic

open Itt_int_base

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< @doc{@terms} >>
declare inf
declare zero
declare succ{'i}
declare lt{'i; 'j}
doc <:doc< @docoff >>

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rewrites

   The following four rewrites give the definition
   of the natural numbers.  The $@inf$ set itself is an
   ordinal construction.
   @end[doc]
>>
prim_rw unfold_zero : zero <--> empty

prim_rw unfold_succ : succ{'i} <--> union{'i; sing{'i}}

prim_rw unfold_inf : inf <-->
   collect{list{unit}; l. list_ind{'l; empty; h, t, g. succ{'g}}}

prim_rw unfold_lt : lt{'i; 'j} <--> mem{'i; 'j}
doc <:doc< @docoff >>

let fold_zero = makeFoldC << zero >> unfold_zero
let fold_succ = makeFoldC << succ{'i} >> unfold_succ

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform zero_df : zero =
   `"0s"

dform succ_df : succ{'i} =
   `"s(" slot{'i} `")"

dform inf_df : inf =
   Nuprl_font!mathbbN `"s"

dform lt_df : parens :: "prec"[prec_compare] :: lt{'i; 'j} =
   pushm[0] szone slot{'i} `" <" hspace slot{'j} ezone popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rules
   @modsubsection{Well-formedness}

   Zero is a set, and the successor of @emph{any} set
   is a set.  Infinity is also a set.
   @end[doc]
>>
interactive zero_isset {| intro [] |} :
   sequent { <H> >- isset{zero} }

interactive succ_isset {| intro [] |} :
   sequent { <H> >- isset{'i} } -->
   sequent { <H> >- isset{succ{'i}} }

interactive inf_isset {| intro [] |} :
   sequent { <H> >- isset{inf} }

interactive succ_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's['z]} } -->
   sequent { <H> >- fun_set{z. succ{'s['z]}} }

doc <:doc<
   @begin[doc]
   @noindent
   The zero is also a number, and the successor is a number
   if it's argument is a number.
   @end[doc]
>>
interactive zero_isnat {| intro [] |} :
   sequent { <H> >- mem{zero; inf} }

interactive succ_isnat {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'i} } -->
   sequent { <H> >- mem{'i; inf} } -->
   sequent { <H> >- mem{succ{'i}; inf} }

doc <:doc<
   @begin[doc]
   @modsubsection{Induction}

   The induction rule performs induction on an
   arbitrary number expression in the goal.  The goal
   must be functional over @emph{all} sets.  The induction
   has the usual cases: to prove $C[i]$ for a number $i$,
   prove $C[@zero]$, and given $C[i]$, prove $C[@succ{i}]$.
   The proof of this rule is rather extensive, but it
   is derived from usual inductive reasoning on sets.
   @end[doc]
>>
interactive nat_elim bind{z. 'C['z]} 'i :
   ["wf"] sequent { <H> >- member{'i; inf} } -->
   ["wf"] sequent { <H> >- fun_prop{z. 'C['z]} } -->
   ["base"] sequent { <H> >- 'C[zero] } -->
   ["step"] sequent { <H>; j: set; u: mem{'j; inf}; v: 'C['j] >- 'C[succ{'j}] } -->
   sequent { <H> >- 'C['i] }

doc <:doc<
   @begin[doc]
   @modsubsection{Functionality}

   The $@lt{i; j}$ relation is functional on its arguments,
   and it is also a restricted proposition.
   @end[doc]
>>
interactive lt_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's1['z]} } -->
   sequent { <H> >- fun_set{z. 's2['z]} } -->
   sequent { <H> >- fun_prop{z. lt{'s1['z]; 's2['z]}} }

interactive lt_restricted {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- restricted{lt{'s1; 's2}} }

doc <:doc<
   @begin[doc]
   @modsubsection{Zero}

   The following three rules characterize the @tt{zero}
   set.  Zero is a number that is smaller than every successor.

   The rules play a crucial rule in forcing the $@inf$ set to be
   infinite.  Induction by itself is not sufficient, because the
   induction rule is valid if all the numbers are equal.  The
   zero rules state that the zero term, at least, is different
   from any successor.
   @end[doc]
>>
interactive zero_member_intro {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'i} } -->
   ["wf"] sequent { <H> >- mem{'i; inf} } -->
   sequent { <H> >- lt{zero; succ{'i}} }

interactive zero_member_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: lt{'i; zero}; <J['x]> >- mem{'i; inf} } -->
   sequent { <H>; x: lt{'i; zero}; <J['x]> >- 'T['x] }

doc <:doc<
   @begin[doc]
   @modsubsection{Successor}

   The following two rules characterize the successor.
   The relation $@lt{@succ{i}; @succ{j}}$ is true if-and-only-if
   $@lt{i; j}$.  With these final rules, we can show that
   $i @neq @succ{i}$, so the set $@inf$ is actually infinite.
   @end[doc]
>>
interactive succ_member_intro1 {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'i} } -->
   ["wf"] sequent { <H> >- isset{'j} } -->
   ["wf"] sequent { <H> >- mem{'i; inf} } -->
   ["wf"] sequent { <H> >- mem{'j; inf} } -->
   sequent { <H> >- lt{'i; 'j} } -->
   sequent { <H> >- lt{succ{'i}; succ{'j}} }

interactive succ_member_elim1 {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: lt{succ{'i}; succ{'j}}; <J['x]> >- isset{'i} } -->
   ["wf"] sequent { <H>; x: lt{succ{'i}; succ{'j}}; <J['x]> >- isset{'j} } -->
   ["wf"] sequent { <H>; x: lt{succ{'i}; succ{'j}}; <J['x]> >- mem{'j; inf} } -->
   sequent { <H>; x: lt{succ{'i}; succ{'j}}; <J['x]>; w: lt{'i; 'j} >- 'T['x] } -->
   sequent { <H>; x: lt{succ{'i}; succ{'j}}; <J['x]> >- 'T['x] }

doc <:doc<
   @begin[doc]
   @tactics

   @begin[description]
   @item{@tactic[natIndT];
      The (@tt{natIndT} @i{t}) tactic performs induction on
      the expression $t$, which must be a well-formed number.}
   @end[description]
   @docoff
   @end[doc]
>>
let natIndT = argfunT (fun t p ->
   let goal = Sequent.concl p in
   let bind = var_subst_to_bind goal t in
      nat_elim bind t)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
