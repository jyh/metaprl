
(*!
 * @begin[doc]
 * @module[Czf_itt_subset]
 *
 * The @tt{Czf_itt_subset} module defines the subset proposition
 * $@\subset{s_1; s_2}$, which is a proposition for any two sets
 * $s_1$ and $s_2$.  The subset is a derived proposition defined
 * as follows.
 *
 * $$@\subset{s_1; s_2} @equiv @dall{x; s_1; @mem{x; s_2}}$$
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
extends Czf_itt_dall

open Base_dtactic

(*! @doc{@terms} *)
declare \subset{'s1; 's2}

(*!
 * @begin[doc]
 * @rewrites
 *
 * The subset is defined using restricted universal quantification.
 * @end[doc]
 *)
prim_rw unfold_subset : ('s1 subset 's2) <--> dall{'s1; x. mem{'x; 's2}}
(*! @docoff *)

prec prec_subset

dform subset_df : parens :: "prec"[prec_subset] :: \subset{'s1; 's2} =
   slot{'s1} `" " Nuprl_font!subseteq `"s " slot{'s2}

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Well-formedness}
 *
 * The subset proposition $@\subset{s_1; s_2}$ is well-formed
 * if $s_1$ and $s_2$ are both sets.
 * @end[doc]
 *)
interactive subset_type {| intro [] |} :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- "type"{.'s1  subset 's2} }

(*!
 * @begin[doc]
 * @modsubsection{Introduction}
 *
 * The subset proposition $@\subset{s_1; s_2}$ is true if every
 * element $@mem{x; s_1}$ is also an element of $s_2$.
 * @end[doc]
 *)
interactive subset_intro {| intro [] |} :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   ["main"] sequent ['ext] { 'H; x: set; y: mem{'x; 's1} >- mem{'x; 's2} } -->
   sequent ['ext] { 'H >- 's1  subset 's2 }

(*!
 * @begin[doc]
 * @modsubsection{Elimination}
 *
 * The elimination form of the proposition $@\subset{s_1; s_2}$
 * takes an element $@mem{x; s_1}$ and it produces a proof that
 * $@mem{x; s_2}$.
 * @end[doc]
 *)
interactive subset_elim {| elim [] |} 'H 's :
   ["wf"] sequent [squash] { 'H; x: 's1 subset 's2; 'J['x] >- isset{'s} } -->
   ["wf"] sequent [squash] { 'H; x: 's1 subset 's2; 'J['x] >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H; x: 's1 subset 's2; 'J['x] >- isset{'s2} } -->
   ["antecedent"] sequent ['ext] { 'H; x: 's1 subset 's2; 'J['x] >- mem{'s; 's1} } -->
   ["main"] sequent ['ext] { 'H; x: 's1 subset 's2; 'J['x]; z: mem{'s; 's2} >- 'C['x] } -->
   sequent ['ext] { 'H; x: 's1  subset 's2; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 * @modsubsection{Functionality}
 *
 * The subset proposition is functional in both set
 * arguments, and it is a restricted proposition.
 * @end[doc]
 *)
interactive subset_res {| intro [] |} :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- restricted{.'s1  subset 's2} }

interactive subset_fun {| intro [] |} :
   sequent ['ext] { 'H >- fun_set{z. 's1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 's2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 's1['z]  subset 's2['z]} }
(*! @docoff *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
