(*!
 * @begin[spelling]
 * unhiding unhidden unhideEqual unhideGoalEqual
 * @end[spelling]
 *
 * @begin[doc]
 * @theory[Itt_hide]
 *
 * The @tt{Itt_hide} module defines a @emph{hidden} type.
 * <<hide{'A}>> hides computational content of $A$.
 * <<hide{'A}>> is inhabited iff and only if $A$ is inhabited.
 * In this case <<hide{'A}>> contains only one element $@it$.
 * That is <<hide{'A}>> means that $A$ is true, but we do not know its
 * computational content.
 * On the other hand,  the sequent
 * $$@sequent{@it; {H; x@colon {} [A]; J}; C}$$
 * is true when $C$ is true (with the assumption that $A$ is true),
 * but extract of $C$ does not contain the witness of $A$.
 * Note that $x$ in this sequent is not witness for $A$, but just $@it$.
 *
 * Hidden types are used to define set in @hreftheory[itt_set].
 *
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
 * Author: Alexei Kopylov
 * @email{kopylov@cs.caltech.edu}
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
   show_loading "Loading Itt_hide%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The @tt{hide} term defines the hidden type.
 * @end[doc]
 *)
declare hide{'A}
(*! @docoff *)

let hide_term = << hide{'a} >>
let hide_opname = opname_of_term hide_term
let is_hide_term = is_dep0_term hide_opname
let dest_hide = dest_dep0_term hide_opname
let mk_hide_term = mk_dep0_term hide_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform hide_df1 : except_mode[src] :: hide{'A} = "[" 'A "]"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext hide(A)
 * by setFormation a A
 * H >- Ui ext A
 *)
prim hideFormation 'H 'A :
   ('A : sequent ['ext] { 'H >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   hide{'A}

(*!
 * @begin[doc]
 * @rules
 * @thysubsection{Equality and typehood}
 *
 * <<hide{'A}>> is a type if $A$ is a type.
 * @end[doc]
 *)
prim hideEquality {| intro_resource []; eqcd_resource |} 'H  :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   sequent ['ext] { 'H >- hide{'A2} = hide{'A1} in univ[i:l] } = it

prim hideType {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{.hide{'A}} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Introduction}
 *
 * A hidden type <<hide{'A}>> is true if $A$ is true.
 * @end[doc]
 *)
prim hideMemberFormation {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'A } -->
   sequent ['ext]   { 'H >- hide{'A} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 *
 * The witness of a provable hidden type is $@it$.
 * @end[doc]
 *)
prim hideMemberEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'A } -->
   sequent ['ext] { 'H >- it IN hide{'A} } =
   it

(*!
 * @begin[doc]
 * @thysubsection{Elimination}
 *
 * The next two rules allow special cases for hidden hypotheses to be
 * unhidden.  The first rule, @tt{unhideEqual}, allows equalities to
 * be unhidden (because the proof can always be inferred), and the
 * @tt{unhideGoalEqual} rule allows hypotheses to be unhidden if an equality
 * is being proved (for the same reason).
 * @end[doc]
 *)
prim unhideEqual 'H 'J 'u :
   ('t['u] : sequent ['ext] { 'H; u: 'x = 'y in 'A; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; u: hide{('x = 'y in 'A)}; 'J['u] >- 'C['u] } =
   't[it]

prim unhideGoalEqual 'H 'J 'u :
   sequent [squash] { 'H; u: 'P; 'J[it] >- 'x[it] = 'y[it] in 'T[it] } -->
   sequent ['ext] { 'H; u: hide{'P}; 'J['u] >- 'x['u] = 'y['u] in 'T['u] } =
   it



(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*!
 * @begin[doc]
 * @docoff
 * @comment{Squash a goal}
 * @end[doc]
 *)
let squashT p =
   if is_squash_goal p then
      idT p
   else
      Sequent.get_tactic_arg p "squash" p

let unhideT i p =
   let u, t = Sequent.nth_hyp p i in
   let t = dest_hide t in
   let j, k = Sequent.hyp_indices p i in
      if is_equal_term t then
         unhideEqual j k u p
      else (* if is_equal_term (Sequent.concl p) then *)
         unhideGoalEqual j k u p

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let typeinf_resource =
   Mp_resource.improve typeinf_resource (hide_term,  Typeinf.infer_map dest_hide)


(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
