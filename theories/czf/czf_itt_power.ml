(*!
 * @spelling{powerT}
 *
 * @begin[doc]
 * @theory[Czf_itt_power]
 *
 * The @tt{Czf_itt_power} module defines @emph{subset} collection.
 * Contrary to the name, the subset collection is @emph{not} a
 * power set, but it has some similarities.  The subset collection
 * constructor has the form $@power{s_1; s_2}$, where $s_1$ and
 * $s_2$ are sets.  If the the canonical forms are $s_1 = @collect{x_1; T_1; f_1[x_1]}$
 * and $s_2 = @collect{x_2; T_2; f_2[x_2]}$, the elements of the
 * power set are the subsets of $s_2$ that are defined by
 * the images of the computable functions in the space $@fun{T_1; T_2}$.
 *
 * $$@power{s_1; s_2} @equiv @collect{g; @fun{T_1; T_2}; @collect{x; T_1; f_2[g(x)]}}$$
 *
 * There is only one significant rule in this module: the
 * axiom of subset collection.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2000 Jason Hickey, Caltech
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
 * @end[license]
 *)

(*! @doc{@parents} *)
include Czf_itt_subset
include Czf_itt_rel
(*! @docoff *)

open Tactic_type

open Itt_equal

open Czf_itt_rel

(************************************************************************
 * TERMS
 ************************************************************************)

(*! @doc{@terms} *)
declare power{'s1; 's2}

(************************************************************************
 * REWRITES
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The subset collection is defined by simultaneous induction
 * on the two set arguments.
 * @end[doc]
 *)
prim_rw unfold_scoll : power{'s1; 's2} <-->
   set_ind{'s1; T1, f1, g1.
      set_ind{'s2; T2, f2, g2.
         collect{.'T1 -> 'T2; x. collect{'T1; y. 'f2 ('x 'y)}}}}

interactive_rw reduce_scoll : power{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
    collect{.'T1 -> 'T2; x. collect{'T1; y. 'f2['x 'y]}}
(*! @docoff *)

let reduce_info =
   [<< power{collect{'t1; x1. 'f1['x1]}; collect{'t2; x2. 'f2['x2]}} >>, reduce_scoll]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform power_df3 : power{'s1; 's2} =
   mathbbP `"(" pushm[0] szone slot{'s1} " " Nuprl_font!rightarrow hspace  slot{'s2} `")" ezone popm

(************************************************************************
 * RULES
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Well-formedness}
 *
 * The subset collection is well-formed if its arguments
 * are sets.
 * @end[doc]
 *)
interactive power_isset1 {| intro_resource [] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- isset{power{'s1; 's2}} }

(*!
 * @begin[doc]
 * @thysubsection{The subset collection axiom}
 *
 * There is an element of the power set for each computable
 * function $@fun{s_1; s_2}$.
 * @end[doc]
 *)
interactive power_thm 'H bind{x. bind{y. 'P['x; 'y]}} 'a 'b :
   ["wf"] sequent [squash] { 'H >- isset{'a} } -->
   ["wf"] sequent [squash] { 'H >- isset{'b} } -->
   ["wf"] sequent [squash] { 'H; x: set; y: set >- "type"{'P['x; 'y]} } -->
   ["wf"] sequent ['ext] { 'H; x: set >- fun_prop{z. 'P['x; 'z]} } -->
   ["wf"] sequent ['ext] { 'H; x: set >- fun_prop{z. 'P['z; 'x]} } -->
   ["antecedent"] sequent ['ext] { 'H; x: set; u: mem{'x; 'a} >- dexists{'b; y. 'P['x; 'y]} } -->
   sequent ['ext] { 'H; z: set; u: mem{'z; power{'a; 'b}}; v: rel{x, y. 'P['x; 'y]; 'a; 'z} >- 'C } -->
   sequent ['ext] { 'H >- 'C }

(*!
 * @begin[doc]
 * @tactics
 *
 * @begin[description]
 * @item{@tactic[powerT];
 *   The (@tt{powerT} @i{t}) tactic applies the @tt{power_@misspelled{thm}} rule.
 *   The argument $t$ is a @hrefterm[rel] term $@rel{x; y; {P[x, y]}; a; b}$
 *   that specifies the proposition $P$ and the sets $a$ and $b$ that are
 *   the arguments to the @tt{power_@misspelled{thm}}.}
 * @end[description]
 * @docoff
 * @end[doc]
 *)
let powerT t p =
   let x, y, prop, a, b = dest_rel (Sequent.concl p) in
   let prop = mk_bind_term y prop in
   let prop = mk_bind_term x prop in
      power_thm (Sequent.hyp_count_addr p) prop a b p

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
(*!
 * @spelling{powerT}
 *
 * @begin[doc]
 * @theory[Czf_itt_power]
 *
 * The @tt{Czf_itt_power} module defines @emph{subset} collection.
 * Contrary to the name, the subset collection is @emph{not} a
 * power set, but it has some similarities.  The subset collection
 * constructor has the form $@power{s_1; s_2}$, where $s_1$ and
 * $s_2$ are sets.  If the the canonical forms are $s_1 = @collect{x_1; T_1; f_1[x_1]}$
 * and $s_2 = @collect{x_2; T_2; f_2[x_2]}$, the elements of the
 * power set are the subsets of $s_2$ that are defined by
 * the images of the computable functions in the space $@fun{T_1; T_2}$.
 *
 * $$@power{s_1; s_2} @equiv @collect{g; @fun{T_1; T_2}; @collect{x; T_1; f_2[g(x)]}}$$
 *
 * There is only one significant rule in this module: the
 * axiom of subset collection.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2000 Jason Hickey, Caltech
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
 * @end[license]
 *)

(*! @doc{@parents} *)
include Czf_itt_subset
include Czf_itt_rel
(*! @docoff *)

open Tactic_type

open Itt_struct

open Czf_itt_rel

(************************************************************************
 * TERMS
 ************************************************************************)

(*! @doc{@terms} *)
declare power{'s1; 's2}

(************************************************************************
 * REWRITES
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The subset collection is defined by simultaneous induction
 * on the two set arguments.
 * @end[doc]
 *)
prim_rw unfold_scoll : power{'s1; 's2} <-->
   set_ind{'s1; T1, f1, g1.
      set_ind{'s2; T2, f2, g2.
         collect{.'T1 -> 'T2; x. collect{'T1; y. 'f2 ('x 'y)}}}}

interactive_rw reduce_scoll : power{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
    collect{.'T1 -> 'T2; x. collect{'T1; y. 'f2['x 'y]}}
(*! @docoff *)

let reduce_info =
   [<< power{collect{'t1; x1. 'f1['x1]}; collect{'t2; x2. 'f2['x2]}} >>, reduce_scoll]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform power_df3 : power{'s1; 's2} =
   mathbbP `"(" pushm[0] szone slot{'s1} " " Nuprl_font!rightarrow hspace  slot{'s2} `")" ezone popm

(************************************************************************
 * RULES
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Well-formedness}
 *
 * The subset collection is well-formed if its arguments
 * are sets.
 * @end[doc]
 *)
interactive power_isset1 {| intro_resource [] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- isset{power{'s1; 's2}} }

(*!
 * @begin[doc]
 * @thysubsection{The subset collection axiom}
 *
 * There is an element of the power set for each computable
 * function $@fun{s_1; s_2}$.
 * @end[doc]
 *)
interactive power_thm 'H bind{x. bind{y. 'P['x; 'y]}} 'a 'b :
   ["wf"] sequent [squash] { 'H >- isset{'a} } -->
   ["wf"] sequent [squash] { 'H >- isset{'b} } -->
   ["wf"] sequent [squash] { 'H; x: set; y: set >- "type"{'P['x; 'y]} } -->
   ["wf"] sequent ['ext] { 'H; x: set >- fun_prop{z. 'P['x; 'z]} } -->
   ["wf"] sequent ['ext] { 'H; x: set >- fun_prop{z. 'P['z; 'x]} } -->
   ["antecedent"] sequent ['ext] { 'H; x: set; u: mem{'x; 'a} >- dexists{'b; y. 'P['x; 'y]} } -->
   sequent ['ext] { 'H; z: set; u: mem{'z; power{'a; 'b}}; v: rel{x, y. 'P['x; 'y]; 'a; 'z} >- 'C } -->
   sequent ['ext] { 'H >- 'C }

(*!
 * @begin[doc]
 * @tactics
 *
 * @begin[description]
 * @item{@tactic[powerT];
 *   The (@tt{powerT} @i{t}) tactic applies the @tt{power_@misspelled{thm}} rule.
 *   The argument $t$ is a @hrefterm[rel] term $@rel{x; y; {P[x, y]}; a; b}$
 *   that specifies the proposition $P$ and the sets $a$ and $b$ that are
 *   the arguments to the @tt{power_@misspelled{thm}}.}
 * @end[description]
 * @docoff
 * @end[doc]
 *)
let powerT t p =
   let x, y, prop, a, b = dest_rel (Sequent.concl p) in
   let prop = mk_bind_term y prop in
   let prop = mk_bind_term x prop in
      power_thm (Sequent.hyp_count_addr p) prop a b p

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
