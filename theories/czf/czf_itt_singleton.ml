(*!
 * @begin[doc]
 * @module[Czf_itt_singleton]
 *
 * The @tt{Czf_itt_singleton} module defines the singleton
 * sets $@sing{s}$, which is a set that contains the single element
 * $s$.  The singleton is used as a building block for pairing,
 * defined in the @hrefmodule[Czf_itt_pair] module.
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
extends Czf_itt_member
(*! @docoff *)

open Printf
open Mp_debug

open Refiner.Refiner.RefineError

open Tactic_type.Sequent
open Tactic_type.Tacticals

open Base_dtactic

let _ =
   show_loading "Loading Czf_itt_singleton%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare sing{'s}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The singleton set $@sing{s}$ is defined as a set
 * with an index type $@unit$, and an element function
 * that returns the set $s$.  Note that @emph{any}
 * non-empty type can be used as the index type.
 * @end[doc]
 *)
prim_rw unfold_sing : sing{'s} <--> collect{unit; x. 's}
(*! @docoff *)

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform sing_df : sing{'s} =
   `"{" slot{'s} `"}"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Well-formedness}
 *
 * The singleton $@sing{s}$ is well-formed if
 * $s$ is a set.
 * @end[doc]
 *)
interactive sing_isset {| intro [] |} :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- isset{sing{'s}} }

(*!
 * @begin[doc]
 * @modsubsection{Introduction and elimination}
 *
 * The @emph{only} element of the singleton set $@sing{s}$ is
 * the set $s$.
 * @end[doc]
 *)
interactive sing_member_elim {| elim [] |} 'H :
   sequent ['ext] { 'H; x: mem{'y; sing{'s}}; 'J['x]; w: eq{'y; 's} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; sing{'s}}; 'J['x] >- 'T['x] }

interactive sing_member_intro {| intro [] |} :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- mem{'s1; sing{'s2}} }

(*!
 * @begin[doc]
 * @modsubsection{Functionality}
 *
 * The singleton is functional in it's set argument.
 * @end[doc]
 *)
interactive sing_fun {| intro [] |} :
   sequent ['ext] { 'H >- fun_set{z. 's['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. sing{'s['z]}} }
(*! @docoff *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
