(*!
 * @spelling{bool esquash esquashT unhidden}
 *
 * @begin[doc]
 * @theory[Itt_esquash]
 *
 * In many cases it is convenient to ``squash'' (omit) the
 * computational content of a proposition.  The ``set'' type
 * defined in the @hreftheory[Itt_set] module defines a squashed
 * proposition $P[x]$ with the type $@set{x; A; P[x]}$.  The
 * elements of the set are the elements in $a @in A$ where the proposition
 * $P[a]$ is true, but the computational content for $P[a]$ is omitted.
 *
 * The @tt{Itt_esquash} module defines a generic squash term
 * $@esquash{P}$.  The elements of the type are the trivial terms
 * $@it$, and two terms $@esquash{P_1}$ and $@esquash{P_2}$ have the
 * @emph{extensional} equality $P_1 @Leftrightarrow P_2$.
 *
 * The definition of the @hrefterm[esquash] term is in terms of
 * the quotient type @hrefterm[quot] in the @hreftheory[Itt_quotient] module
 * and the Boolean type in the @hreftheory[Itt_bool] module.  The definition
 * may look strange:
 *
 * $$@esquash{P} @equiv @btrue = @bfalse @in @quot{@bool; b_1; b_2; (b_1 = b_2 @in @bool) @vee P}.$$
 *
 * The quotient type $@quot{@bool; b_1; b_2; (b_1 = b_2 @in @bool) @vee P}$ equates
 * $@btrue$ and $@bfalse$ if $P$ is true.  Otherwise, $@btrue @neq @bfalse$
 * and the equality type is empty.
 *
 * A simpler construction (and the traditional @Nuprl construction)
 * defines the squash type with the set type:
 *
 * $$@squash{P} @equiv @set{x; @unit; P}.$$
 *
 * The elements of @hrefterm[esquash] and @tt{squash} are the same,
 * but the equalities differ, $@esquash{P_1} = @esquash{P_2} @in @univ{i}$ if
 * $P_1 @Leftrightarrow P_2$, and $@squash{P_1} = @squash{P_2} @in @univ{i}$ if
 * $P_1 = P_2 @in @univ{i}$.  This is because the quotient type uses
 * an @emph{extensional} equality on it's equivalence relation, and
 * the @tt{set} type uses an @emph{intensional} equality on it's predicate.
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
 * Author: Jason Hickey
 * @email{jyh@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Itt_void
include Itt_unit
include Itt_quotient
include Itt_set
include Itt_bool
include Itt_logic
(*! @docoff *)

open Tactic_type
open Tactic_type.Conversionals

open Itt_equal
open Itt_void
open Itt_unit

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{esquash_bool} term defines the quotient type,
 * and the @tt{esquash} term defines the squash predicate $P$.
 * @end[doc]
 *)
define unfold_esquash_bool : esquash_bool{'P} <-->
   (quot b1, b2 : bool // (('b1 = 'b2 in bool) or 'P))

define unfold_esquash : esquash{'P} <--> (btrue = bfalse in esquash_bool{'P})
(*! @docoff *)

prec prec_esquash

dform esquash_bool : except_mode[src] :: esquash_bool{'P} =
   `"esquash_bool(" slot{'P} `")"

dform esquash_df : parens :: "prec"[prec_esquash] :: except_mode[src] :: esquash{'P} =
   Nuprl_font!downarrow slot{'P}

let fold_esquash_bool = makeFoldC << esquash_bool{'P} >> unfold_esquash_bool
let fold_esquash = makeFoldC << esquash{'P} >> unfold_esquash

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Typehood and equality}
 *
 * The @tt{esquash_bool} term $@esquashbool{P}$ is well-formed if
 * $P$ is a type; it contains the terms $@btrue$ and $@bfalse$.
 * @end[doc]
 *)
interactive esquash_bool_type {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'P} } -->
   sequent ['ext] { 'H >- "type"{esquash_bool{'P}} }

interactive esquash_bool_univ {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'P IN univ[i:l] } -->
   sequent ['ext] { 'H >- esquash_bool{'P} IN univ[i:l] }

interactive esquash_bool_true {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'P} } -->
   sequent ['ext] { 'H >- btrue IN esquash_bool{'P} }

interactive esquash_bool_false {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'P} } -->
   sequent ['ext] { 'H >- bfalse IN esquash_bool{'P} }

(*!
 * @begin[doc]
 * The @tt{esquash} term inhabits the type universe $@univ{i}$
 * if the proposition $P$ is also in $@univ{i}$.
 * @end[doc]
 *)
interactive esquash_type {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'P} } -->
   sequent ['ext] { 'H >- "type"{esquash{'P}} }

interactive esquash_univ {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'P IN univ[i:l] } -->
   sequent ['ext] { 'H >- esquash{'P} IN univ[i:l] }

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * The $@esquash{P}$ proposition is true if $P$ is true.
 * However, this rule is too strong to add to the
 * @hrefresource[intro_resource] directly.  Instead, the
 * @hreftactic[esquashT] tactic is defined below to
 * apply this rule.
 * @end[doc]
 *)
interactive esquash_intro 'H :
   [main] sequent [squash] { 'H >- 'P } -->
   sequent ['ext] { 'H >- esquash{'P} }

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The element in the $@esquash{P_1}$ term is always the term
 * $@it$.  The assumption $x@colon @esquash{P}$ can be ``exposed''
 * if the proof in not needed, as in the proof of $@void$.  As the type theory
 * evolves, it seems likely that we will allow the hypothesis to be
 * exposed in @hrefterm[squash] sequent.
 * @end[doc]
 *)
interactive esquash_equal_elim 'H 'J :
   [main] sequent [squash] { 'H; x: 'P1; 'J[it] >- 't1[it] = 't2[it] in 'T3[it] } -->
   sequent ['ext] { 'H; x: esquash{'P1}; 'J['x] >- 't1['x] = 't2['x] in 'T3['x] }

interactive esquash_void_elim 'H 'J :
   [main] sequent [squash] { 'H; x: 'P1; 'J[it] >- void } -->
   sequent ['ext] { 'H; x: esquash{'P1}; 'J['x] >- void }

interactive esquash_esquash_elim 'H 'J :
   [main] sequent [squash] { 'H; x: 'P1; 'J[it] >- esquash{'P2[it]} } -->
   sequent ['ext] { 'H; x: esquash{'P1}; 'J['x] >- esquash{'P2['x]} }

let d_esquash_elim i p =
   let goal = Sequent.concl p in
   let j, k = Sequent.hyp_indices p i in
      if is_equal_term goal then
         esquash_equal_elim j k p
      else if is_void_term goal then
         esquash_void_elim j k p
      else
         esquash_esquash_elim j k p

let resource elim += (<< esquash{'P} >>, d_esquash_elim)

(*!
 * @begin[doc]
 * The $@esquash{P}$ hypothesis can also be unhidden if
 * $P$ is an equality judgment, or $@void$, or $@unit$, or a nested
 * @hrefterm[esquash] proposition (or in general if the proof
 * can be recovered).
 * @end[doc]
 *)
interactive esquash_equal_elim2 {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; x: ('t1 = 't2 in 'T3); 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: esquash{.'t1 = 't2 in 'T3}; 'J['x] >- 'C['x] }

interactive esquash_void_elim2 {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; x: esquash{void}; 'J['x] >- 'C['x] }

interactive esquash_unit_elim2 {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: esquash{unit}; 'J['x] >- 'C['x] }

interactive esquash_esquash_elim2 {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; x: esquash{'P}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: esquash{esquash{'P}}; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 * @thysubsection{Extensional equality}
 *
 * Two squashed propositions $@esquash{P_1}$ and $@esquash{P_2}$
 * are equal if both $P_1$ and $P_2$ are types, and $P_1 @Leftrightarrow P_2$.
 * @end[doc]
 *)
interactive esquash_equal_intro {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- 'P1 IN univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'P2 IN univ[i:l] } -->
   [main] sequent [squash] { 'H; x: 'P1 >- 'P2 } -->
   [main] sequent [squash] { 'H; x: 'P2 >- 'P1 } -->
   sequent ['ext] { 'H >- esquash{'P1} = esquash{'P2} in univ[i:l] }

(*!
 * @begin[doc]
 * @thysubsection{Set elimination}
 *
 * The standard rule for set elimination @hrefrule[setElimination]
 * can be overridden with the following more useful rule.
 * @end[doc]
 *)
interactive set_elim {| elim_resource [] |} 'H 'J :
   [main] sequent ['ext] { 'H; x: 'T; z: esquash{'P['x]}; 'J['x] >- 'C['x] } -->
   sequent ['ext] { 'H; x: { y: 'T | 'P['y] }; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 * @tactics
 *
 * @begin[description]
 * @item{@tactic[esquashT];
 *   The @tt{esquashT} tactic applies the @hrefrule[esquash_intro] rule}
 * @end[description]
 * @docoff
 * @end[doc]
 *)
let esquashT p =
   esquash_intro (Sequent.hyp_count_addr p) p

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
