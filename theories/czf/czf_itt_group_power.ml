(*!
 * @spelling{power}
 *
 * @begin[doc]
 * @theory[Czf_itt_group_power]
 *
 * The @tt{Czf_itt_group_power} module defines the power operation
 * in a group, i.e., it describes $x^n = x * x * ... * x$.
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
include Czf_itt_group
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
   show_loading "Loading Czf_itt_group_power%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare power{'g; 'z; 'n}
(*! @docoff *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The @tt{power} is defined by induction.
 * @end[doc]
 *)
prim_rw unfold_power : power{'g; 'z; 'n} <-->
   ind{'n; i, j. op{'g; inv{'g; 'z}; power{'g; 'z; ('n +@ 1)}}; id{'g}; k, l. op{'g; 'z; power{'g; 'z; ('n -@ 1)}}}
(*! @docoff *)

let fold_power = makeFoldC << power{'g; 'z; 'n} >> unfold_power

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform power_df : parens :: except_mode[src] :: power{'g; 'z; 'n} =
   `"power(" slot{'g} `"; " slot{'z}  `"; " slot{'n} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Well-formedness}
 *
 * The $@power{g; z; n}$ is well-formed if $g$ is a label,
 * $z$ is a set, and $n$ is an integer in ITT.
 * @end[doc]
 *)
interactive power_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'z} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{power{'g; 'z; 'n}} }

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * If $z$ is a member of $@car{g}$, then $@power{g; z; n}$
 * is also in $@car{g}$.
 * @end[doc]
 *)
interactive power_mem {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent [squash] { 'H >- isset{'z} } -->
   sequent ['ext] { 'H >- mem{'z; car{'g}} } -->
   sequent ['ext] { 'H >- mem{power{'g; 'z; 'n}; car{'g}} }

(*!
 * @begin[doc]
 * @thysubsection{Functionality}
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
(*! @docoff *)

(* x ^ (n + 1) * x ^ (-1) = x ^ n *)
interactive power_less {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; power{'g; 'x; ('n +@ 1)}; inv{'g; 'x}}; power{'g; 'x; 'n}} }

(* x ^ n * x = x ^ (n + 1) *)
interactive power_more {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; power{'g; 'x; 'n}; 'x}; power{'g; 'x; ('n +@ 1)}} }

(*!
 * @begin[doc]
 * @thysubsection{Power reduction}
 *
 * $x^m * x^n = x^{m + n}$
 * @end[doc]
 *)
interactive power_reduce1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'm IN int } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- eq{op{'g; power{'g; 'x; 'm}; power{'g; 'x; 'n}}; power{'g; 'x; ('m +@ 'n)}} }

(*! @docoff *)
(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
