(*!
 * @spelling{dexists}
 *
 * @begin[doc]
 * @module[Czf_itt_dexists]
 *
 * The @tt{Czf_itt_dexists} theory defines @emph{restricted}
 * existential quantification.  The syntax of the operator
 * is $@dexists{x; s; P[x]}$, where $s$ is a set, and $P[x]$
 * is a functional proposition for any set argument $x$.
 * The proposition is true if $P[a]$ is true for @emph{some} element
 * $@mem{a; s}$.
 *
 * The restricted universal quantification is coded as
 * an implication on the elements of $s$.
 *
 * $$@dexists{x; @collect{y; T; f[y]}; P[x]} @equiv @prod{x; T; P[x]}$$
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
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * @email{jyh@cs.cornell.edu}
 * @end[license]
 *)

(*! @doc{@parents} *)
extends Czf_itt_sep
extends Czf_itt_set_ind
(*! @docoff *)

open Printf
open Mp_debug

open Refiner.Refiner.RefineError

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent
open Var

open Base_dtactic

open Itt_logic
open Itt_rfun

let _ =
   show_loading "Loading Czf_itt_dexists%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare "dexists"{'T; x. 'A['x]}
(*! @docoff *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The existential is defined by set induction on the set
 * argument as a dependent product type.
 * @end[doc]
 *)
prim_rw unfold_dexists : "dexists"{'s; x. 'A['x]} <-->
   set_ind{'s; T, f, g. x: 'T * 'A['f 'x]}

interactive_rw reduce_dexists : "dexists"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T * 'A['f['t]])
(*! @docoff *)

let resource reduce +=
   << "dexists"{collect{'T; x. 'f['x]}; y. 'A['y]} >>, reduce_dexists

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform dexists_df : parens :: "prec"[prec_lambda] :: "dexists"{'s; x. 'A} =
   pushm[0] Nuprl_font!"exists" slot{'x} " " Nuprl_font!member `"s " slot{'s} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Well-formedness}
 *
 * The proposition $@dexists{x; s; P[x]}$ is well-formed
 * if $s$ is a set, and $P[x]$ is a well-formed proposition
 * for @emph{any} set argument $x$.
 * @end[doc]
 *)
interactive dexists_type {| intro [] |} 'y :
   ["wf"] sequent [squash] { 'H >- isset{'s} } -->
   ["wf"] sequent [squash] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."dexists"{'s; x. 'A['x]}} }

(*!
 * @begin[doc]
 * @modsubsection{Introduction}
 *
 * The existential $@dexists{x; s; P[x]}$ is true if
 * it is well-formed and if $P[a]$ is true for some
 * element $@mem{a; s}$.
 * @end[doc]
 *)
interactive dexists_intro {| intro [] |} 'z 'w :
   ["wf"] sequent [squash] { 'H; w: set >- "type"{'A['w]} } -->
   ["wf"] sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   ["main"] sequent ['ext] { 'H >- member{'z; 's} } -->
   ["antecedent"] sequent ['ext] { 'H >- 'A['z] } -->
   sequent ['ext] { 'H >- "dexists"{'s; x. 'A['x]} }

(*!
 * @begin[doc]
 * @modsubsection{Elimination}
 *
 * The proof of the existential $@dexists{x; s; P[x]}$ has two parts:
 * an element $@mem{a; s}$, and a proof $P[a]$.  The elimination form
 * produces these parts.
 * @end[doc]
 *)
interactive dexists_elim {| elim [] |} 'H 'x 'z 'v 'w :
   ["wf"] sequent [squash] { 'H; x: "dexists"{'s; y. 'A['y]}; 'J['x] >- isset{'s} } -->
   ["wf"] sequent [squash] { 'H; x: "dexists"{'s; y. 'A['y]}; 'J['x]; z: set >- "type"{'A['z]} } -->
   ["wf"] sequent ['ext] { 'H; x: "dexists"{'s; y. 'A['y]}; 'J['x] >- fun_prop{z. 'A['z]} } -->
   ["main"] sequent ['ext] { 'H;
                    x: "dexists"{'s; y. 'A['y]};
                    'J['x];
                    z: set;
                    v: mem{'z; 's};
                    w: 'A['z]
                    >- 'C['x]
                  } -->
   sequent ['ext] { 'H; x: "dexists"{'s; y. 'A['y]}; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 * @modsubsection{Functionality}
 *
 * The existential is functional in both its set and proposition
 * arguments.
 * @end[doc]
 *)
interactive dexists_fun {| intro [] |} :
   sequent ['ext] { 'H >- fun_set{z. 'A['z]} } -->
   sequent ['ext] { 'H; z: set >- fun_prop{x. 'B['z; 'x]} } -->
   sequent ['ext] { 'H; z: set >- fun_prop{x. 'B['x; 'z]} } -->
   ["wf"] sequent [squash] { 'H; z: set; x: set >- "type"{'B['z; 'x]} } -->
   sequent ['ext] { 'H >- fun_prop{z. "dexists"{'A['z]; y. 'B['z; 'y]}} }

(*!
 * @begin[doc]
 * @modsubsection{Restriction}
 *
 * The existential is a restricted formula because it is
 * a quantification over the @emph{index} type of the set
 * argument.
 * @end[doc]
 *)
interactive dexists_res2 {| intro [] |} :
   ["wf"]   sequent [squash] { 'H >- isset{'A} } -->
   sequent [squash] { 'H; u: set >- restricted{'B['u]} } -->
   sequent ['ext] { 'H >- restricted{."dexists"{'A; y. 'B['y]}} }
(*! @docoff *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
