(*!
 * @begin[doc]
 * @module[Itt_bisect]
 *
 * The @tt{Itt_bisect} module derives a binary intersection
 * $@bisect{A; B}$ from the intersection @hrefterm[isect] defined
 * in the @hrefmodule[Itt_isect] theory, and the Boolean values
 * defined in the @hrefmodule[Itt_bool] theory.
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

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Itt_isect
extends Itt_bool
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

open Var
open Tactic_type
open Tactic_type.Tacticals

open Base_dtactic

open Perv

open Itt_equal
open Itt_struct


(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The definition of the binary intersection $@bisect{A; B}$
 * is an intersection over the Booleans.
 * @end[doc]
 *)
define unfold_bisect : bisect{'A; 'B} <-->
                          "isect"{bool; x. ifthenelse{'x; 'A; 'B}}
(*! @docoff *)

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_bisect

dform bisect_df : except_mode[src] :: parens :: "prec"[prec_bisect] :: bisect{'A; 'B} =
   slot["le"]{'A} `" " cap space slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Typehood and equality}
 *
 * The binary intersection $@bisect{A; B}$ is well-formed if both $A$
 * and $B$ are types.
 * @end[doc]
 *)
interactive bisectEquality {| intro []; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- bisect{'A1; 'B1} = bisect{'A2; 'B2} in univ[i:l] }

interactive bisectType {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{bisect{'A; 'B}} }

(*!
 * Formation.
 * @docoff
 *)
interactive bisectFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(*!
 * @begin[doc]
 * @modsubsection{Membership}
 *
 * Two terms $x$ and $y$ are equal in the binary intersection
 * $@bisect{A; B}$ if they are equal in both $A$ and $B$.  Put another
 * way, the elements of the binary intersection are the terms that
 * are members of both $A$ and $B$.
 * @end[doc]
 *)
interactive bisectMemberEquality {| intro []; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- 'x = 'y in 'A } -->
   [wf] sequent [squash] { 'H >- 'x = 'y in 'B } -->
   sequent ['ext] { 'H >- 'x = 'y in bisect{'A; 'B} }

(*!
 * @begin[doc]
 * @modsubsection{Elimination}
 *
 * The elimination rule for an assumption $x@colon @bisect{A; B}$ states that  $x$ can be replaced by
 * $a @in A$ or by $b @in B$.
 * @end[doc]
 *)
(*!@docoff *)

interactive bisectElimination_eq 'H 'J 'u 'v bind{x,HACK.bind{a,b.'C['x;'a;'b;'HACK]}} :
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x]; a: 'A; u: 'a = 'x in 'A;
                                                   b: 'B; v: 'b = 'x in 'B >- 'C['x;'a;'b;it] } -->
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x] >- 'C['x;'x;'x;it] }

let bisectEliminationT n p =
   let u,v = maybe_new_vars2 p "u" "v" in
   let i, j = Sequent.hyp_indices p n in
   let x,_ = Sequent.nth_hyp p n in
   let x_var = mk_var_term x in
   let bind =  get_with_arg p in
      if is_bind2_term bind then
         let bind2 = mk_bind2_term x "HACK" bind in
            bisectElimination_eq i j u v bind2 p
      else
         raise (RefineError
           ("bisectElimination", StringTermError ("required the bind term:",<<bind{a,b.'C['a;'b]}>>)))

let bisectEliminationT n p =
  let n = if n<0 then (Sequent.hyp_count p) + n + 1 else n in
    (bisectEliminationT n thenT thinIfThinningT [-3;-1;n]) p

let resource elim += (<<bisect{'A; 'B}>>,bisectEliminationT)

(*! *)

interactive bisectElimination 'H 'J bind{a,b.'C['a;'b]} :
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x]; a: 'A; b: 'B >- 'C['a;'b] } -->
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x] >- 'C['x;'x] }

(*!
 * @begin[doc]
 *
 * The elimination rule has also two simpler forms.
 * The first produces a witness that $x @in A$, and the second produces a witness
 * for $x @in B$.
 * @end[doc]
 *)


interactive bisectEliminationLeft (*{| elim [SelectOption 1] |}*) 'H 'J 'a 'u 'b 'v:
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x]; a: 'A; u: 'a = 'x in 'A; b: 'B; v: 'b = 'x in 'B >- 'C['a] } -->
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x] >- 'C['x] }

interactive bisectEliminationRight (*{| elim [SelectOption 2] |}*) 'H 'J 'a 'u 'b 'v :
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x]; a: 'A; u: 'a = 'x in 'A; b: 'B; v: 'b = 'x in 'B >- 'C['b] } -->
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x] >- 'C['x] }

let bisectEliminationT n p =
   let n = if n<0 then (Sequent.hyp_count p) + n + 1 else n in
   try
      let sel = get_sel_arg p in
      let a,u,b,v = maybe_new_vars4 p "a" "u" "b" "v" in
      let i, j = Sequent.hyp_indices p n in
      let r =
         if sel = 1 then bisectEliminationLeft else
         if sel = 2 then bisectEliminationRight else
            raise (RefineError ("bisectElimination", StringError ("select option is out of range ([1,2])")))
      in (r i j a u b v thenT thinIfThinningT [-3;-1;n]) p
   with RefineError ("get_attribute",_) ->
      try bisectEliminationT n p
      with RefineError ("get_attribute",_) ->
         raise (RefineError
            ("bisectElimination", StringTermError ("need a select option or a bind term:",<<bind{a,b.'C['a;'b]}>>)))

let resource elim += (<<bisect{'A; 'B}>>,bisectEliminationT)


(*!
 * @begin[doc]
 * @modsubsection{Subtyping}
 *
 * The binary intersection $@bisect{A; B}$ is covariant
 * in both $A$ and $B$.
 * @end[doc]
 *)
interactive bisectSubtypeLeft 'H :
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent [squash] { 'H >- subtype{'A; 'C} } -->
   sequent ['ext] { 'H >- subtype{bisect{'A; 'B}; 'C} }

interactive bisectSubtypeRight 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- subtype{'B; 'C} } -->
   sequent ['ext] { 'H >- subtype{bisect{'A; 'B}; 'C} }

interactive bisectSubtypeBelow 'H :
   sequent [squash] { 'H >- subtype{'C; 'A} } -->
   sequent [squash] { 'H >- subtype{'C; 'B} } -->
   sequent ['ext] { 'H >- subtype{'C; bisect{'A; 'B}} }
(*! @docoff *)

(*
 * Subtyping.
 *)
let intro_bisect_aboveT p =
   let j = get_sel_arg p in
      if j = 1 then
         bisectSubtypeLeft  (Sequent.hyp_count_addr p) p
      else
         bisectSubtypeRight  (Sequent.hyp_count_addr p) p

let bisect_above_term = << subtype{bisect{'A; 'B}; 'C} >>

let intro_bisect_belowT p =
   bisectSubtypeBelow (Sequent.hyp_count_addr p) p

let bisect_below_term = << subtype{'C; bisect{'A; 'B}} >>

let resource intro += [
   bisect_above_term, wrap_intro intro_bisect_aboveT;
   bisect_below_term, wrap_intro intro_bisect_belowT
]

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
