(*!
 * @spelling{cycgroup}
 *
 * @begin[doc]
 * @theory[Czf_itt_cyclic_subgroup]
 *
 * The @tt{Czf_itt_cyclic_subgroup} module defines cyclic subgroups.
 * A cyclic subgroup of group $g$ is a subgroup of $g$ whose carrier
 * is the collection of $x^n (n @in @int)$ for some $x @in @car{g}$.
 *
 * $x^n$ is defined by induction on $n$ as
 * $$
 * @begin[array, l]
 * @line{@item{@power{g; z; n} @equiv}}
 * @line{@item{@space @space @space
 *   @ind{n; i; j; @op{g; @inv{g; z}; @power{g; z; (n + 1)}}; @id{g}; k; l; @op{g; z; @power{g; z; (n - 1)}}}}}
 * @end[array]
 * $$
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
include Czf_itt_subgroup
include Itt_int_base
(*! @docoff *)

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print
open Printf
open Mp_debug

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

let _ =
   show_loading "Loading Czf_itt_cyclic_subgroup%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare power{'g; 'z; 'n}
declare cyc_subg{'s; 'g; 'a}
(*! @docoff *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The @tt{power} is defined by induction. The @tt{cycsubg} is defined
 * by @tt{groupbvd}.
 * @end[doc]
 *)
prim_rw unfold_power : power{'g; 'z; 'n} <-->
   ind{'n; i, j. op{'g; inv{'g; 'z}; power{'g; 'z; ('n +@ 1)}}; id{'g}; k, l. op{'g; 'z; power{'g; 'z; ('n -@ 1)}}}

prim_rw unfold_cyc_subg : cyc_subg{'s; 'g; 'a} <-->
   (group{'s} & group{'g} & mem{'a; car{'g}} & group_bvd{'s; 'g; collect{int; x. power{'g; 'a; 'x}}})
(*   (mem{'a; car{'g}} & group_bvd{'s; 'g; collect{int; x. power{'g; 'a; 'x}}}) *)
(*! @docoff *)

let fold_power = makeFoldC << power{'g; 'z; 'n} >> unfold_power
let fold_cyc_subg = makeFoldC << cyc_subg{'s; 'g; 'a} >> unfold_cyc_subg

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform power_df : parens :: except_mode[src] :: power{'g; 'z; 'n} =
   `"power(" slot{'g} `"; " slot{'z}  `"; " slot{'n} `")"

dform cyc_subg_df : except_mode[src] :: cyc_subg{'s; 'g; 'a} =
   `"cyclic_subgroup(" slot{'s} `"; " slot{'g} `"; " slot{'a} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Typehood for power operation}
 *
 * The $@power{g; z; n}$ is well-formed if $g$ is a label,
 * $z$ is a set, and $n$ is an integer in ITT.
 * @end[doc]
 *)
interactive power_wf1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'z} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{power{'g; 'z; 'n}} }

(*!
 * @begin[doc]
 * @thysubsection{Power membership}
 *
 * If $z$ is a member of $@car{g}$, then $@power{g; z; n}$
 * is also in $@car{g}$.
 * @end[doc]
 *)
interactive power_wf2 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent [squash] { 'H >- isset{'z} } -->
   sequent ['ext] { 'H >- mem{'z; car{'g}} } -->
   sequent ['ext] { 'H >- mem{power{'g; 'z; 'n}; car{'g}} }

(*!
 * @begin[doc]
 * @thysubsection{Power functionality}
 *
 * The @tt{power} is functional in its set argument.
 * @end[doc]
 *)
interactive power_fun {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- fun_set{z. 'f['z]} } -->
   sequent ['ext] { 'H; z: set >- mem{'f['z]; car{'g}} } -->
   sequent ['ext] { 'H >- fun_set{z. power{'g; 'f['z]; 'n}} }

interactive power_equiv_fun {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- equiv_fun_set{car{'g}; eqG{'g}; z. 'f['z]} } -->
   sequent ['ext] { 'H >- equiv_fun_set{car{'g}; eqG{'g}; z. power{'g; 'f['z]; 'n}} }
(*! @docoff *)

interactive power_equiv_fun1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- equiv_fun_set{car{'g}; eqG{'g}; z. power{'g; 'z; 'n}} }

(* x ^ (n + 1) * x ^ (-1) = x ^ n *)
interactive power_property1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; eqG{'g}; op{'g; power{'g; 'x; ('n +@ 1)}; inv{'g; 'x}}; power{'g; 'x; 'n}} }

(* x ^ n * x = x ^ (n + 1) *)
interactive power_property2 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; eqG{'g}; op{'g; power{'g; 'x; 'n}; 'x}; power{'g; 'x; ('n +@ 1)}} }

(*!
 * @begin[doc]
 * @thysubsection{Power simplification}
 *
 * $x^m * x^n = x^{m + n}$
 * @end[doc]
 *)
interactive power_simplify {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'm IN int } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; eqG{'g}; op{'g; power{'g; 'x; 'm}; power{'g; 'x; 'n}}; power{'g; 'x; ('m +@ 'n)}} }

(*!
 * @begin[doc]
 * @thysubsection{Typehood for cyclic subgroups}
 *
 * The $@cycsubg{s; g; a}$ is well-formed if $s$ and $g$ are labels
 * and $a$ is a set.
 * @end[doc]
 *)
interactive cyc_subg_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- "type"{cyc_subg{'s; 'g; 'a}} }

(*!
 * @begin[doc]
 * @thysubsection{Introduction for cyclic subgroups}
 *
 * The proposition $@cycsubg{s; g; a}$ is true if it is well-formed,
 * $s$ and $g$ are groups, $@mem{a; @car{g}}$,
 *  $@equal{@car{s}; @collect{x; @int; @power{g; a; x}}}$,
 * $@op{s; a; b}$ is defined as $@op{g; a; b}$ for $a, b @in @car{s}$,
 * and any two elements of $h$ are equivalent iff they are equivalent in $g$.
 * @end[doc]
 *)
interactive cyc_subg_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- group{'s} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- equal{car{'s}; collect{int; x. power{'g; 'a; 'x}}} } -->
   sequent ['ext] { 'H; b: set; c: set; x: mem{'b; car{'s}}; y: mem{'c; car{'s}} >- equiv{car{'s}; eqG{'s}; op{'s; 'b; 'c}; op{'g; 'b; 'c}} } -->
   sequent ['ext] { 'H; d: set; e: set; u: equiv{car{'s}; eqG{'s}; 'd; 'e} >- equiv{car{'g}; eqG{'g}; 'd; 'e} } -->
   sequent ['ext] { 'H; p: set; q: set; x: mem{'p; car{'s}}; y: mem{'q; car{'s}}; v: equiv{car{'g}; eqG{'g}; 'p; 'q} >- equiv{car{'s}; eqG{'s}; 'p; 'q} } -->
   sequent ['ext] { 'H >- cyc_subg{'s; 'g; 'a} }

(*!
 * @begin[doc]
 * @thysubsection{Properties of cyclic subgroups}
 *
 * A cyclic subgroup is a subgroup.
 * @end[doc]
 *)
interactive cycsubg_subgroup 'H 'a :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- group{'s} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- cyc_subg{'s; 'g; 'a} } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} }

(*! @docoff *)
(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*!
 * @begin[doc]
 * @tactics
 *
 * @begin[description]
 * @item{@tactic[cycsubgSubgroupT];
 *    The tactic applies the @hrefrule[cycsubg_subgroup] rule
 *    and proves a group is a subgroup by showing it is a
 *    cyclic subgroup.}
 * @end[description]
 * @docoff
 * @end[doc]
 *)
let cycsubgSubgroupT t p =
   cycsubg_subgroup (hyp_count_addr p) t p

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
