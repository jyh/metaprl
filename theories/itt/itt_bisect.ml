(*!
 * @begin[doc]
 * @theory[Itt_bisect]
 *
 * The @tt{Itt_bisect} module derives a binary intersection
 * $@bisect{A; B}$ from the intersection @hrefterm[isect] defined
 * in the @hreftheory[Itt_isect] theory, and the Boolean values
 * defined in the @hreftheory[Itt_bool] theory.
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
include Itt_isect
include Itt_bool
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

open Itt_equal

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
 * @thysubsection{Typehood and equality}
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
 * @thysubsection{Membership}
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
 * @thysubsection{Elimination}
 *
 * The elimination rule has two forms for an assumption $x@colon @bisect{A; B}$.
 * The first produces a witness that $x @in A$, and the second produces a witness
 * for $x @in B$.
 * @end[doc]
 *)
interactive bisectElimination 'H 'J bind{z,a,b.'C['z;'a;'b]} 'u 'v :
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x]; a: 'A; u: 'a = 'x in 'A;
                                                   b: 'B; v: 'b = 'x in 'B >- 'C['x;'a;'b] } -->
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x] >- 'C['x;'x;'x] }

interactive bisectElimination0 'H 'J 'a 'b 'u 'v :
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x]; a: 'A; u: 'a = 'x in 'A;
                                                   b: 'B; v: 'b = 'x in 'B >- 'C['x] } -->
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x] >- 'C['x] }

interactive bisectEliminationLeft 'H 'J 'a 'b 'u 'v :
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x]; a: 'A; u: 'a = 'x in 'A;
                                                   b: 'B; v: 'b = 'x in 'B >- 'C['a] } -->
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x] >- 'C['x] }

interactive bisectEliminationRight 'H 'J 'a 'b 'u 'v :
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x]; a: 'A; u: 'a = 'x in 'A;
                                                   b: 'B; v: 'b = 'x in 'B >- 'C['b] } -->
   sequent ['ext] { 'H; x: bisect{'A; 'B}; 'J['x] >- 'C['x] }

(*!
 * D tactic.
 * @docoff
 *)

let elim_bisectT i p =
   let j, k = Sequent.hyp_indices p i in
   try
      let c = get_with_arg p in
      let u, v = maybe_new_vars2 p  "u" "v" in
         bisectElimination j k c u v p
   with RefineError _ ->
      let sel = get_sel_arg p in
      let a, b, u, v = maybe_new_vars4 p "a" "b" "u" "v" in
         if sel = 1 then
           bisectEliminationLeft j k a b u v p
         else if sel = 2 then
           bisectEliminationRight j k a b u v p
         else
           bisectElimination0 j k a b u v p


let bisect_term = << bisect{'A; 'B} >>

let resource elim += (bisect_term, elim_bisectT)



(*!
 * @begin[doc]
 * @thysubsection{Subtyping}
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

let resource intro += (bisect_above_term, intro_bisect_aboveT)

let intro_bisect_belowT p =
   bisectSubtypeBelow (Sequent.hyp_count_addr p) p

let bisect_below_term = << subtype{'C; bisect{'A; 'B}} >>

let resource intro += (bisect_below_term, intro_bisect_belowT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
