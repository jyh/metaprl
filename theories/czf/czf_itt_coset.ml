(*!
 * @spelling{lcoset rcoset}
 *
 * @begin[doc]
 * @theory[Czf_itt_coset]
 *
 * The @tt{Czf_itt_coset} module defines the @emph{left coset} and
 * the @emph{right coset}. If $h$ is a subgroup of $g$ and
 * $@mem{a; @car{g}}$, then the set of $a * h$ for which
 * $h @in @car{h}$ is the left coset of $h$ containing $a$, and the
 * set of $h * a$ for which $h @in @car{h}$ is the right coset of
 * $h$ containing $a$. The elements of the left coset are the
 * elements of $x @in @car{g}$ which is equivalent with $@op{g; a; y}$
 * for some $y @in @car{h}$. The elements of the right coset are the
 * elements of $x @in @car{g}$ which is equivalent with $@op{g; y; a}$
 * for some $y @in @car{h}$.
 *
 * The @tt{lcoset} and @tt{rcoset} are defined by @tt{sep} instead of
 * @tt{setbvd}. The @tt{setbvd} definition $@setbvd{x; @car{h}; @op{g; a; x}}$
 * for $@lcoset{h; g; a}$ looks correct at the first sight, but the
 * introduction and elimination rules for @tt{setbvd} all refers to
 * equality rather that equivalence, which is not suitable for groups.
 * The $@lcoset{h; g; a}$ and $@rcoset{h; g; a}$ are defined by
 * separation as
 * $$
 * @sep{x; @car{'g}; @dexists{y; car{'h}; @mem{@pair{'x; @op{'g; 'a; 'y}}; @eqG{'g}}}}
 * $$
 * and
 * $$
 * @sep{x; @car{'g}; @dexists{y; car{'h}; @mem{@pair{'x; @op{'g; 'y; 'a}}; @eqG{'g}}}}
 * $$
 *
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 2002 Xin Yu, Caltech
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
 * Author: Xin Yu
 * @email{xiny@cs.caltech.edu}
 * @end[license]
 *)

(*! @doc{@parents} *)
include Czf_itt_group
include Czf_itt_subgroup
include Czf_itt_set_bvd
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Sequent
open Tactic_type.Tacticals
open Var
open Mptop

open Base_dtactic
open Base_auto_tactic

let _ =
   show_loading "Loading Czf_itt_coset%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare lcoset{'h; 'g; 'a}
declare rcoset{'h; 'g; 'a}
(*! @docoff *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The @tt{lcoset} and @tt{rcoset} terms are defined by separation.
 * @end[doc]
 *)
prim_rw unfold_lcoset : lcoset{'h; 'g; 'a} <-->
   sep{car{'g}; x. "dexists"{car{'h}; y. mem{pair{'x; op{'g; 'a; 'y}}; eqG{'g}}}}

prim_rw unfold_rcoset : rcoset{'h; 'g; 'a} <-->
   sep{car{'g}; x. "dexists"{car{'h}; y. mem{pair{'x; op{'g; 'y; 'a}}; eqG{'g}}}}
(*! @docoff *)

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform lcoset_df : parens :: except_mode[src] :: lcoset{'h; 'g; 'a} =
   `"lcoset(" slot{'h} `"; " slot{'g} `"; " slot{'a} `")"

dform rcoset_df : parens :: except_mode[src] :: rcoset{'h; 'g; 'a} =
   `"rcoset(" slot{'h} `"; " slot{'g} `"; " slot{'a} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Well-formedness}
 *
 * The $@lcoset{h; g; a}$ and $@rcoset{h; g; a}$ are well-formed
 * if $h$ and $g$ are labels, $a$ is a set, and $g$ is a group.
 * @end[doc]
 *)
interactive lcoset_isset {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{lcoset{'h; 'g; 'a}} }

interactive rcoset_isset {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{rcoset{'h; 'g; 'a}} }

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * A set $x$ is a member of $@lcoset{h; g; a}$ if the
 * left coset is well-formed, $@mem{a; @car{g}}$,
 * $@mem{x; @car{g}}$, $@subgroup{h; g}$, and there
 * exists a set $y$ such that $y$ is a member of
 * $@car{h}$ and $x$ is equivalent to $@op{g; a; y}$
 * in $@car{g}$.
 * @end[doc]
 *)
interactive lcoset_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g} } -->
   sequent ['ext] { 'H >- exst y: set. (mem{'y; car{'h}} & equiv{car{'g}; eqG{'g}; 'x; op{'g; 'a; 'y}}) } -->
   sequent ['ext] { 'H >- mem{'x; lcoset{'h; 'g; 'a}} }

interactive rcoset_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g} } -->
   sequent ['ext] { 'H >- exst y: set. (mem{'y; car{'h}} & equiv{car{'g}; eqG{'g}; 'x; op{'g; 'y; 'a}}) } -->
   sequent ['ext] { 'H >- mem{'x; rcoset{'h; 'g; 'a}} }

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The elimination form for the left coset
 * $@mem{y; @lcoset{h; g; a}}$ implies $@mem{y; @car{g}}$
 * and also produces a witness $@mem{z; @car{h}}$ for which
 * $@equiv{@car{g}; @eqG{g}; y; @op{g; a; z}}$.
 * @end[doc]
 *)
interactive lcoset_elim {| elim [] |} 'H 'J :
   sequent [squash] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- 'h IN label } -->
   sequent [squash] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- 'g IN label } -->
   sequent [squash] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- isset{'a} } -->
   sequent [squash] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- isset{'y} } -->
   sequent ['ext] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- subgroup{'h; 'g} } -->
   sequent ['ext] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x]; u: mem{'y; car{'g}}; z: set; v: mem{'z; car{'h}}; w: equiv{car{'g}; eqG{'g}; 'y; op{'g; 'a; 'z}} >- 'C['x] } -->
   sequent ['ext] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- 'C['x] }

interactive rcoset_elim {| elim [] |} 'H 'J :
   sequent [squash] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- 'h IN label } -->
   sequent [squash] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- 'g IN label } -->
   sequent [squash] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- isset{'a} } -->
   sequent [squash] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- isset{'y} } -->
   sequent ['ext] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- subgroup{'h; 'g} } -->
   sequent ['ext] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x]; u: mem{'y; car{'g}}; z: set; v: mem{'z; car{'h}}; w: equiv{car{'g}; eqG{'g}; 'y; op{'g; 'z; 'a}} >- 'C['x] } -->
   sequent ['ext] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 * @thysubsection{Theorems}
 *
 * $h$ is a subgroup of group $g$. Both the left and right
 * coset of $h$ containing $a$ are subsets of the underlying
 * set of $g$.
 * @end[doc]
 *)
interactive lcoset_subset {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g} } -->
   sequent ['ext] { 'H >- subset{lcoset{'h; 'g; 'a}; car{'g}} }

interactive rcoset_subset {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g} } -->
   sequent ['ext] { 'H >- subset{rcoset{'h; 'g; 'a}; car{'g}} }

(*! @docoff *)
(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
