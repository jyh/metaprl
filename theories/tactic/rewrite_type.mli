(*
 * This is the basic rewrite data type.
 * A file with this name is required for every theory.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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
 * jyh@cs.cornell.edu
 *)

include Perv

open Refiner.Refiner.Refine

open Tactic_type
open Sequent

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

type env
type conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Justification for rewrites.
 *)
declare rewrite_just

(*
 * The basic rewrite axiom.
 * BUG: jyh: I don't know why we need the extra param here.
 *)
axiom rewriteAxiom 'x : "rewrite"{'x; 'x}

(*
 * Sequent version of rewrite proposition.
 *)
axiom rewriteSequentAxiom 'H : sequent ['ext] { 'H >- "rewrite"{'x; 'x} }

(*
 * Sequent replacement.
 *)
axiom rewriteHypCut 'H 'J 'T1 :
   sequent ['ext] { 'H; x: 'T1; 'J['x] >- 'C['x] } -->
   sequent ['ext] { 'H >- "rewrite"{'T1; 'T2} } -->
   sequent ['ext] { 'H; x: 'T2; 'J['x] >- 'C['x] }

axiom rewriteConclCut 'H 'T1 :
   sequent ['ext] { 'H >- 'T1 } -->
   sequent ['ext] { 'H >- "rewrite"{'T1; 'T2} } -->
   sequent ['ext] { 'H >- 'T2 }

(*
axiom rewriteContextCut 'H 'J (lambda{v. 'T['v]}) :
   "sequent"{'ext; ."context"[H:v]{'T["concl"{'C; ."concl"}]}} -->
   "sequent"{'ext; ."context"[H:v]{."concl"{."rewrite"{.'T[rewrite_just]; ."context"[J:v]{rewrite_just}}; concl}}} -->
   "sequent"{'ext; ."context"[H:v]{."context"[J:v]{."concl"{'C; ."concl"}}}}
*)

(************************************************************************
 * OPERATIONS                                                           *
 ************************************************************************)

(*
 * Operations on the environment mirror operations from Sequent.
 *)
val env_term : env -> term
val env_goal : env -> term

(*
 * Apply a rewrite.
 *)
val rw : conv -> int -> tactic

(*
 * Create a conversion from a basic rewrite.
 * This function is required by filter_prog.
 *)
val rewrite_of_rewrite : prim_rewrite -> conv

(*
 * Create a conversion from a conditional rewrite.
 * This function is required by filter_prog.
 *)
val rewrite_of_cond_rewrite : prim_cond_rewrite -> string array * term list -> conv

(*
 * Sequencing.
 *)
val prefix_andthenC : conv -> conv -> conv
val prefix_orelseC : conv -> conv -> conv

(*
 * Identity.
 *)
val idC : conv

(*
 * Pull out the argument.
 *)
val funC : (env -> conv) -> conv

(*
 * Apply a conversion at an address.
 *)
val addrC : int list -> conv -> conv

(*
 * Apply at conversion at the outermost terms where it does not fail.
 *)
val higherC : conv -> conv

(*
 * Two versions of cut.
 * foldC t conv: cuts in the new term t, and uses conv to
 *    solve the resulting goal.
 * cutC t: just cuts in the new goal
 *)
val foldC : term -> conv -> conv
val cutC : term -> conv

(*
 * Create a fold operation automatically.
 *)
val makeFoldC : term -> conv -> conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
