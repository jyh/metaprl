(*!
 * @spelling{sexists}
 *
 * @begin[doc]
 * @module[Czf_itt_sexists]
 *
 * The @tt{Czf_itt_sexists} module defines the @emph{unrestricted}
 * existential quantification $@sexists{x; P[x]}$.  The proposition
 * $P[x]$ must be well-formed for any set argument.  The existential
 * is true, if $P[a]$ is true for some set $a$.
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
extends Czf_itt_and
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
   show_loading "Loading Czf_itt_sexists%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare "sexists"{x. 'A['x]}
(*! @docoff *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The unrestricted existential is defined with the type-theoretic
 * existential @hrefterm[exists] from the @hrefmodule[Itt_logic]
 * module.
 * @end[doc]
 *)
prim_rw unfold_sexists : "sexists"{x. 'A['x]} <--> (exst x: set. 'A['x])
(*! @docoff *)

let fold_sexists = makeFoldC << "sexists"{x. 'A['x]} >> unfold_sexists

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform sexists_df : except_mode[src] :: parens :: "prec"[prec_lambda] :: "sexists"{x. 'A} =
   math_sexists{'x; 'A}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Well-formedness}
 *
 * The unrestricted existential $@sexists{x; P[x]}$ is well-formed
 * if $P[x]$ is a well-formed proposition for any set argument $x$.
 * @end[doc]
 *)
interactive sexists_type {| intro [] |} :
   sequent [squash] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."sexists"{x. 'A['x]} } }

(*!
 * @begin[doc]
 * @modsubsection{Introduction}
 *
 * The existential $@sexists{x; P[x]}$ is true if $P[a]$
 * is true for some set $a$.
 * @end[doc]
 *)
interactive sexists_intro  {| intro [] |} 'z :
   ["wf"]   sequent ['ext] { 'H >- isset{'z} } -->
   ["main"] sequent ['ext] { 'H >- 'A['z] } -->
   ["wf"]   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H >- "sexists"{x. 'A['x]} }

(*!
 * @begin[doc]
 * @modsubsection{Elimination}
 *
 * The proof of the existential $@sexists{x; P[x]}$ is a pair of a witness
 * set $a$ and a proof $P[a]$.
 * @end[doc]
 *)
interactive sexists_elim {| elim [] |} 'H :
   sequent ['ext] { 'H;
                    z: set;
                    w: 'A['z];
                    'J[pair{'z; 'w}]
                    >- 'T[pair{'z; 'w}]
                  } -->
   sequent ['ext] { 'H; x: "sexists"{y. 'A['y]}; 'J['x] >- 'T['x] }
(*! @docoff *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
