(*!
 * @spelling{bool esquash esquashT unhidden squashes}
 *
 * @begin[doc]
 * @module[Itt_esquash]
 *
 * The @hrefterm[squash] operator in @hrefmodule[Itt_squash] theory
 * allows us to ``squash'' (omit) the computational content
 * of a proposition. But in many cases in addition to squashing
 * the computational context we want to be able to squash the
 * intensional term structure as well.
 *
 * The @tt{Itt_esquash} module defines a generic squash term
 * $@esquash{P}$.  The elements of the type are the trivial terms
 * $@it$ (provided $P$ itself is non-empty), and two terms
 * $@esquash{P_1}$ and $@esquash{P_2}$ have the @emph{extensional}
 * equality $P_1 @Leftrightarrow P_2$.
 *
 * For more information on the @tt[esquash] operator see @cite["Nog02a,Nog02b"].
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * Authors: Jason Hickey @email{jyh@cs.cornell.edu}
 *          Aleksey Nogin @email{nogin@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Itt_void
extends Itt_equal
extends Itt_squash
extends Itt_struct
(*! @docoff *)

open Tactic_type
open Tactic_type.Tacticals

open Base_dtactic
open Base_auto_tactic

open Itt_equal
open Itt_squash

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{esquash} operator @i{extensionally squashes} a proposition.
 * @end[doc]
 *)
declare esquash{'P}
(*! @docoff *)

dform esquash_df : except_mode[src] :: esquash{'P} =
   math_esquash{'P}

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Typehood and equality}
 *
 * The @tt{esquash} term inhabits the type universe $@univ{i}$
 * if the proposition $P$ is also in $@univ{i}$.
 * @end[doc]
 *)
prim esquash_type {| intro [AutoMustComplete] |} :
   [wf] sequent [squash] { 'H >- "type"{'P} } -->
   sequent ['ext] { 'H >- "type"{esquash{'P}} } =
   it

(*!
 * @begin[doc]
 * Two squashed propositions $@esquash{'A}$ and $@esquash{'B}$
 * are equal if both are types, and if each one implies another.
 * @end[doc]
 *)
prim esquash_equal {| intro [SelectOption 0]; eqcd |} :
   [wf] sequent [squash] { 'H >- esquash{'P1} in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- esquash{'P2} in univ[i:l] } -->
   sequent [squash] { 'H; x: esquash{'P1} >- esquash{'P2} } -->
   sequent [squash] { 'H; x: esquash{'P2} >- esquash{'P1} } -->
   sequent ['ext] { 'H >- esquash{'P1} = esquash{'P2} in univ[i:l] } =
   it

prim esquash_univ {| intro [AutoMustComplete] |} :
   [wf] sequent [squash] { 'H >- 'P in univ[i:l] } -->
   sequent ['ext] { 'H >- esquash{'P} in univ[i:l] } =
   it

(*!
 * @begin[doc]
 * @modsubsection{Introduction}
 *
 * The $@esquash{P}$ proposition is true if $P$ is true.
 * However, this rule is too strong to add to the
 * @hrefresource[intro_resource] directly.  Instead, the
 * @hreftactic[esquashT] tactic is defined below to
 * apply this rule.
 * @end[doc]
 *)
prim esquash_intro {| intro [AutoMustComplete] |} :
   [main] sequent [squash] { 'H >- squash{'P} } -->
   sequent ['ext] { 'H >- esquash{'P} } =
   it

(*!
 * @begin[doc]
 * @modsubsection{Membership}
 *
 * The element in the $@esquash{P}$ term is always the term
 * $@it$.
 * @end[doc]
 *)
prim esquash_elim {| elim [] |} 'H :
   ( 't['x] : sequent ['ext] { 'H; x: esquash{'A}; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: esquash{'A}; 'J['x] >- 'C['x] } =
   't[it]

(*!
 * @begin[doc]
 * It can also be formulated as an introduction rule.
 * @end[doc]
 *)
interactive esquash_mem {| intro []; squash |} :
   sequent [squash] { 'H >- esquash{'A} } -->
   sequent ['ext] { 'H >- it in esquash{'A} }

(*!
 * @begin[doc]
 * @modsubsection{Elimination}
 * When a proposition is a type (i.e, functional), its @tt[esquash] is
 * true if and only if its @tt[squash] is true.
 * @end[doc]
 *)
prim esquash :
   [wf] sequent [squash] { 'H >- "type"{'P} } -->
   sequent [squash] { 'H >- esquash{'P} } -->
   sequent ['ext] { 'H >- squash{'P} } =
   it

(*!
 * @begin[doc]
 * The following rule is equivalent to the previous one.
 * @end[doc]
 *)
interactive unesquash 'H :
   [wf] sequent [squash] { 'H; x: esquash{'P}; 'J[it] >- "type"{'P} } -->
   sequent ['ext] { 'H; x: squash{'P}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: esquash{'P}; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 * The $@esquash{@void}$ can not be inhabited.
 * @end[doc]
 *)
interactive esquash_void_elim {| elim [] |} 'H :
   sequent ['ext] { 'H; x: esquash{void}; 'J['x] >- 'C['x] }

interactive esquash_equal_intro {| intro [] |} 'x :
   [wf] sequent [squash] { 'H >- 'P1 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'P2 in univ[i:l] } -->
   [main] sequent [squash] { 'H; x: 'P1 >- 'P2 } -->
   [main] sequent [squash] { 'H; x: 'P2 >- 'P1 } -->
   sequent ['ext] { 'H >- esquash{'P1} = esquash{'P2} in univ[i:l] }

(*!
 * @begin[doc]
 * @tactics
 *
 * @begin[description]
 * @item{@tactic[esquashT];
 *   The @tt[esquashT] 0 tactic applies the @hrefrule[esquash] rule and
 *   @tt[esquashT] @i{i} applies the @hrefrule[unesquash] rule.}
 * @end[description]
 * @docoff
 * @end[doc]
 *)
let esquashT i =
   if i = 0 then esquash else unesquash i

let esquashAutoT =
   autoT thenT tryT (onSomeHypT esquashT orelseT esquash) thenT autoT

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
