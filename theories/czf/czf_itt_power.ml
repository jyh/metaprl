doc <:doc<
   @begin[doc]
   @module[Czf_itt_power]

   The @tt[Czf_itt_power] module defines @emph{subset} collection.
   Contrary to the name, the subset collection is @emph{not} a
   power set, but it has some similarities.  The subset collection
   constructor has the form $@power{s_1; s_2}$, where $s_1$ and
   $s_2$ are sets.  If the canonical forms are $s_1 = @collect{x_1; T_1; f_1[x_1]}$
   and $s_2 = @collect{x_2; T_2; f_2[x_2]}$, the elements of the
   power set are the subsets of $s_2$ that are defined by
   the images of the computable functions in the space $@fun{T_1; T_2}$.

   $$@power{s_1; s_2} @equiv @collect{g; @fun{T_1; T_2}; @collect{x; T_1; f_2[g(x)]}}$$

   There is only one significant rule in this module: the
   axiom of subset collection.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2000 Jason Hickey, Caltech

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
   @email{jyh@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Czf_itt_subset
extends Czf_itt_rel
doc docoff

open Refiner.Refiner.TermMan

open Tactic_type
open Tactic_type.Tacticals
open Dtactic
open Top_conversionals

open Czf_itt_rel

(************************************************************************
 * TERMS
 ************************************************************************)

doc <:doc< @doc{@terms} >>
declare power{'s1; 's2}

(************************************************************************
 * REWRITES
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rewrites

   The subset collection is defined by simultaneous induction
   on the two set arguments.
   @end[doc]
>>
prim_rw unfold_scoll : power{'s1; 's2} <-->
   set_ind{'s1; T1, f1, g1.
      set_ind{'s2; T2, f2, g2.
         collect{.'T1 -> 'T2; x. collect{'T1; y. 'f2 ('x 'y)}}}}

interactive_rw reduce_scoll {| reduce |} :
   power{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   collect{.'T1 -> 'T2; x. collect{'T1; y. 'f2['x 'y]}}

doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform power_df3 : power{'s1; 's2} =
   mathbbP `"(" pushm[0] szone slot{'s1} " " Nuprl_font!rightarrow hspace  slot{'s2} `")" ezone popm

(************************************************************************
 * RULES
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rules
   @modsubsection{Well-formedness}

   The subset collection is well-formed if its arguments
   are sets.
   @end[doc]
>>
interactive power_isset1 {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- isset{power{'s1; 's2}} }

doc <:doc<
   @begin[doc]
   @modsubsection{The subset collection axiom}

   There is an element of the power set for each computable
   function $@fun{s_1; s_2}$.
   @end[doc]
>>
interactive power_thm bind{x. bind{y. 'P['x; 'y]}} 'a 'b :
   ["wf"] sequent { <H> >- isset{'a} } -->
   ["wf"] sequent { <H> >- isset{'b} } -->
   ["wf"] sequent { <H>; x: set; y: set >- "type"{'P['x; 'y]} } -->
   ["wf"] sequent { <H>; x: set >- fun_prop{z. 'P['x; 'z]} } -->
   ["wf"] sequent { <H>; x: set >- fun_prop{z. 'P['z; 'x]} } -->
   ["antecedent"] sequent { <H>; x: set; u: mem{'x; 'a} >- dexists{'b; y. 'P['x; 'y]} } -->
   sequent { <H>; z: set; u: mem{'z; power{'a; 'b}}; v: rel{x, y. 'P['x; 'y]; 'a; 'z} >- 'C } -->
   sequent { <H> >- 'C }

doc <:doc<
   @begin[doc]
   @tactics

   @begin[description]
   @item{@tactic[powerT];
     The (@tt{powerT} @i{t}) tactic applies the @tt{power_@misspelled{thm}} rule.
     The argument $t$ is a @hrefterm[rel] term $@rel{x; y; {P[x, y]}; a; b}$
     that specifies the proposition $P$ and the sets $a$ and $b$ that are
     the arguments to the @tt{power_@misspelled{thm}}.}
   @end[description]
   @docoff
   @end[doc]
>>
let powerT = funT (fun p ->
   let x, y, prop, a, b = dest_rel (Sequent.concl p) in
   let prop = mk_xbind_term y prop in
   let prop = mk_xbind_term x prop in
      power_thm prop a b)

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
