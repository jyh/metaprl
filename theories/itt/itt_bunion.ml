(*!
 * @begin[doc]
 * @theory[Itt_bunion]
 *
 * The @tt{Itt_bunion} module defines a binary union $@bunion{A; B}$
 * of type types $A$ and $B$.  The elements include the elements of $A$
 * as well as the elements of $B$.  Two elements are equal
 * if they are equal in @emph{either} of the types.
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
include Itt_tunion
include Itt_bool
include Itt_struct
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
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_dtactic

open Itt_equal
open Itt_struct

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The binary union is defined using the @hrefterm[tunion]
 * over the space of Booleans.
 * @end[doc]
 *)
define unfold_bunion : bunion{'A; 'B} <-->
                          tunion{bool; x. ifthenelse{'x; 'A; 'B}}
(*! @docoff *)

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_bunion

dform bunion_df : parens :: "prec"[prec_bunion] :: except_mode[src] :: bunion{'A; 'B} =
   slot["le"]{'A} `" " cup space slot{'B}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

let fold_bunion = makeFoldC << bunion{'A; 'B} >> unfold_bunion

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Typehood and equality}
 *
 * The union $@bunion{A; B}$ is well-formed if
 * both $A$ and $B$ are types.
 * @end[doc]
 *)
interactive bunionEquality {| intro []; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- bunion{'A1; 'B1} = bunion{'A2; 'B2} in univ[i:l] }

interactive bunionType {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{bunion{'A; 'B}} }

(*!
 * Formation.
 * @docoff
 *)
interactive bunionFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * Two terms are equal in the binary union if they are equal
 * in either type.
 * @end[doc]
 *)
interactive bunionMemberEqualityLeft {| intro [SelectOption 1]; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- 'x = 'y in 'A } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- 'x = 'y in bunion{'A; 'B} }

interactive bunionMemberEqualityRight {| intro [SelectOption 2]; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- 'x = 'y in 'B } -->
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- 'x = 'y in bunion{'A; 'B} }

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The elimination form retains the limitations of the
 * general union elimination @hrefrule[tunionElimination]: it
 * can be used only for equality judgments.  The elimination form
 * for a union type $@bunion{A; B}$ produces two cases: one for
 * membership in $A$, and another for membership in $B$.
 * @end[doc]
 *)
interactive bunionElimination {| elim [ThinOption thinT] |} 'H 'J 'y :
   [main] sequent [squash] { 'H; x: bunion{'A; 'B}; 'J['x]; y: 'A >- 't1['y] = 't2['y] in 'C['y] } -->
   [main] sequent [squash] { 'H; x: bunion{'A; 'B}; 'J['x]; y: 'B >- 't1['y] = 't2['y] in 'C['y] } -->
   sequent ['ext] { 'H; x: bunion{'A; 'B}; 'J['x] >- 't1['x] = 't2['x] in 'C['x] }

let thinLastT n = thinT (-1) thenT tryT (thinT n)

interactive bunionElimination_eq {| elim [ThinOption thinLastT] |} 'H 'J 'y :
   [main] sequent [squash] { 'H; x: bunion{'A; 'B}; 'J['x]; y: 'A; u:'y='x in bunion{'A; 'B} >- squash{'C['y]} } -->
   [main] sequent [squash] { 'H; x: bunion{'A; 'B}; 'J['x]; y: 'B; u:'y='x in bunion{'A; 'B} >- squash{'C['y]} } -->
   sequent ['ext] { 'H; x: bunion{'A; 'B}; 'J['x] >- squash{'C['x]} }
(*! @docoff *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
