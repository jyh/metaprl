(*!
 *
 * @begin[doc]
 * @theory[Itt_set]
 *
 * The @tt{Itt_set} module defines a ``set'' type, or more precisely,
 * it defines a type by quantified @emph{separation}.  The form of the type is
 * $@set{x; T; P[x]}$, where $T$ is a type, and $P[x]$ is a type for
 * any element $x @in T$.  The elements of the set type are those elements
 * of $x @in T$ where the proposition $P[x]$ is true.
 *
 * The set type is a ``squash'' type: the type is similar to the
 * dependent product $x@colon T @times P[x]$ (Section @reftheory[Itt_dprod]),
 * but the proof $P[x]$ is omitted (squashed).  The set type $@set{x; T; P[x]}$
 * is always a subtype of $T$.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 *
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
 * @email{jyh@cs.caltech.edu}
 *
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Itt_squash
include Itt_equal
include Itt_unit
include Itt_subtype
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

open Tactic_type
open Tactic_type.Tacticals
open Var

open Base_dtactic

open Itt_squash
open Itt_struct
open Itt_equal
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_set%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{set} term defines the set type.
 * @end[doc]
 *)
declare set{'A; x. 'B['x]}
(*! @docoff *)

let set_term = << { a: 'A | 'B['a] } >>
let set_opname = opname_of_term set_term
let is_set_term = is_dep0_dep1_term set_opname
let dest_set = dest_dep0_dep1_term set_opname
let mk_set_term = mk_dep0_dep1_term set_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform set_df1 : {x:'A | 'B} =
   pushm[3] `"{ " bvar{'x} `":" slot{'A} `" | " slot{'B} `"}" popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext { a:A | B }
 * by setFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
prim setFormation 'H 'a 'A :
   [wf] sequent [squash] { 'H >- 'A = 'A in univ[i:l] } -->
   ('B['a] : sequent ['ext] { 'H; a: 'A >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   { a: 'A | 'B['a] }

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Equality and typehood}
 *
 * The set type $@set{x; A; B[x]}$ is a type if $A$ is a type,
 * and $B[x]$ is a type for any $x @in A$.  Equality of the set
 * type is @emph{intensional}.  Two set types are equal only if their
 * parts are equal.  An alternative formulation would be to allow sets
 * $@set{x; A_1; B_1[x]}$ and $@set{x; A_2; B_2[x]}$ to be equal
 * if $A_1 = A_2 @in @univ{i}$ and $B_1[x] @Leftrightarrow B_2[x]$ for
 * any $x @in A_2$.
 * @end[doc]
 *)
prim setEquality {| intro_resource []; eqcd_resource |} 'H 'x :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[i:l] } -->
   sequent ['ext] { 'H >- { a1:'A1 | 'B1['a1] } = { a2:'A2 | 'B2['a2] } in univ[i:l] } =
   it

prim setType {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A1} } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- "type"{'B1['x]} } -->
   sequent ['ext] { 'H >- "type"{.{ a1:'A1 | 'B1['a1] }} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * A set type $@set{x; A; B[x]}$ is true if there is an element $a @in A$
 * where $B[x]$ is true.
 * @end[doc]
 *)
prim setMemberFormation {| intro_resource [] |} 'H 'a 'z :
   [wf] sequent [squash] { 'H >- 'a = 'a in 'A } -->
   [main] sequent [squash]   { 'H >- 'B['a] } -->
   [wf] sequent [squash] { 'H; z: 'A >- "type"{'B['z]} } -->
   sequent ['ext]   { 'H >- { x:'A | 'B['x] } } =
   'a

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * Two terms $a_1$ and $a_2$ are equal in the set type $@set{a; A; B[a]}$
 * if they are equal in $A$ and also $B[a_1]$ is true.
 * @end[doc]
 *)
prim setMemberEquality {| intro_resource []; eqcd_resource |} 'H 'x :
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   [assertion] sequent [squash] { 'H >- 'B['a1] } -->
   [wf] sequent [squash] { 'H; x: 'A >- "type"{'B['x]} } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in { a:'A | 'B['a] } } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * An assumption with a set type $u@colon @set{x; A; B[x]}$ asserts two facts:
 * that $u @in A$ and $B[u]$.  However, the proof of $B[u]$ is unavailable.  The
 * << squash{'B['u]} >> hypothesis states that $B[u]$ is true, but its proof is
 * omitted.
 * @end[doc]
 *)
prim setElimination {| elim_resource [] |} 'H 'J 'u 'v :
   ('t : sequent ['ext] { 'H; u: 'A; v: squash{'B['u]}; 'J['u] >- 'T['u] }) -->
   sequent ['ext] { 'H; u: { x:'A | 'B['x] }; 'J['u] >- 'T['u] } =
   't

(*!
 * @begin[doc]
 * @thysubsection{Subtyping}
 *
 * The set type $@set{x; A; B[x]}$ is always a subtype of $A$ if
 * the set type is really a type.  This rule is added to the
 * @hrefresource[subtype_resource].
 * @end[doc]
 *)
prim set_subtype {| intro_resource [] |} 'H :
   sequent [squash] { 'H >- "type"{ { a: 'A | 'B['a] } } } -->
   sequent ['ext] { 'H >- subtype{ { a: 'A | 'B['a] }; 'A } } =
   it

(*! @docoff *)


(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let typeinf_resource =
   Mp_resource.improve typeinf_resource (set_term,  infer_univ_dep0_dep1 dest_set)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

let set_subtypeT p =
   set_subtype (Sequent.hyp_count_addr p) p

let sub_resource =
   Mp_resource.improve
   sub_resource
   (LRSubtype ([<< { a: 'A | 'B['a] } >>, << 'A >>], set_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
