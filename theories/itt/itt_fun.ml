(*!
 * @spelling{independentFunctionElimination}
 *
 * @begin[doc]
 * @module[Itt_fun]
 *
 * The @tt{Itt_fun} module defines the non-dependent function type.
 * The function type is @emph{derived} from the dependent-function
 * type @hrefmodule[Itt_dfun], which is in turn derived from the
 * very-dependent function @hrefmodule[Itt_rfun].
 *
 * The non-dependent function $@fun{A; B}$ is the type of functions
 * with domain $A$, and range $B$.  It is equivalent to the
 * dependent function space $@fun{x; A; B}$, where $x$ is not
 * bound in $B$.
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
extends Itt_equal
extends Itt_dfun
(*! @docoff *)

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Var

open Typeinf
open Base_dtactic

open Itt_equal
open Itt_subtype
open Itt_rfun
open Itt_dfun

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_fun%t"

(* debug_string DebugLoad "Loading itt_fun..." *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The non-dependent function $@fun{A; B}$ is defined as the
 * dependent function $@fun{x; A; B}$ (where $x$ is new).
 * @end[doc]
 *)
prim_rw unfold_fun : ('A -> 'B) <--> (x: 'A -> 'B)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Typehood and equality}
 *
 * The non-dependent function has an intensional type equality.
 * @end[doc]
 *)
interactive independentFunctionEquality {| intro []; eqcd |} 'H :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- ('A1 -> 'B1) = ('A2 -> 'B2) in univ[i:l] }

(*
 * Typehood.
 *)
interactive independentFunctionType {| intro [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A1} } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- "type"{'B1} } -->
   sequent ['ext] { 'H >- "type"{. 'A1 -> 'B1 } }

(*!
 * @begin[doc]
 * @modsubsection{Introduction}
 *
 * The propositional interpretation of the function space $@fun{A; B}$
 * is the implication term @hrefterm[implies], $@implies{A; B}$.
 * The proposition is true if it is a type, and for any proof of $A$,
 * there is a proof of $B$.
 * @end[doc]
 *)
interactive independentLambdaFormation {| intro [] |} 'H 'z :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [main] ('b['z] : sequent ['ext] { 'H; z: 'A >- 'B }) -->
   sequent ['ext] { 'H >- 'A -> 'B }

(*!
 * @begin[doc]
 * @modsubsection{Membership}
 *
 * The elements in the function space $@fun{A; B}$ are the
 * @hrefterm[lambda] functions.  The space $@fun{A; B}$ must be a
 * type, and the body of the function must be an $B$ for any argument
 * in $A$.
 * @end[doc]
 *)
interactive independentLambdaEquality {| intro []; eqcd |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; x: 'A >- 'b1['x] = 'b2['x] in 'B } -->
   sequent ['ext] { 'H >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in 'A -> 'B }

(*!
 * @begin[doc]
 * @modsubsection{Elimination}
 *
 * There are two elimination forms.  The @tt{independentFunctionElimination}
 * rule is more appropriate for the propositional interpretation of the function
 * space $@fun{A; B}$: if there is a proof of $A$, then there is also a proof
 * of $B$.  The second form, @tt{independentFunctionElimination2}, is
 * more appropriate for the functional application to a specific argument $a @in A$.
 * @end[doc]
 *)
interactive independentFunctionElimination 'H 'J 'f 'y :
   [assertion] ('a : sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'A }) -->
   [main] ('t['f; 'y] : sequent ['ext] { 'H; f: 'A -> 'B; 'J['f]; y: 'B >- 'T['f] }) -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'T['f] }

(*
 * Explicit function elimination.
 *)
interactive independentFunctionElimination2 'H 'J 'f 'y 'z 'a :
   [wf] sequent [squash] { 'H; f: 'A -> 'B; 'J['f] >- 'a IN 'A } -->
   [main] ('t['y; 'z] : sequent ['ext] { 'H; f: 'A -> 'B; 'J['f]; y: 'B; z: 'y = ('f 'a) in 'B >- 'T['f] }) -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'T['f] }

(*!
 * @begin[doc]
 * @modsubsection{Combinator equality}
 *
 * Applications have an intensional equality; they are equal if their
 * functions and arguments are equal.
 * @end[doc]
 *)
interactive independentApplyEquality {| intro[]; eqcd |} 'H ('A -> 'B) :
   [wf] sequent [squash] { 'H >- 'f1 = 'f2 in 'A -> 'B } -->
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- ('f1 'a1) = ('f2 'a2) in 'B }

(*!
 * @begin[doc]
 * @modsubsection{Subtyping}
 *
 * The function space is @emph{contravariant} in their domains,
 * and @emph{covariant} in their ranges.
 *
 * @docoff
 * @end[doc]
 *)
interactive independentFunctionSubtype {| intro [] |} 'H :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 -> 'B1); ('A2 -> 'B2) } }

(*
 * H >- Ui ext A -> B
 * by independentFunctionFormation
 *
 * H >- Ui ext A
 * H >- Ui ext B
 *)
interactive independentFunctionFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] }

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * Application equality depends on our infering a type.
 *)
let d_apply_equalT p =
   let _, app, _ = dest_equal (Sequent.concl p) in
   let f, _ = dest_apply app in
   let f_type =
      try get_with_arg p with
         RefineError _ ->
            infer_type p f
   in
   let tac =
      if is_rfun_term f_type then
         rfunction_applyEquality
      else if is_dfun_term f_type then
         applyEquality
      else if is_fun_term f_type then
         independentApplyEquality
      else
         raise (RefineError ("d_apply_equalT", StringTermError ("inferred type is not a function type", f_type)))
   in
      tac (Sequent.hyp_count_addr p) f_type p

let apply_equal_term = << 'f1 'a1 = 'f2 'a2 in 'T >>

(*
 * Typehood of application depends on the ability to infer a type.
 *)
let d_apply_typeT p =
   let app = dest_type_term (Sequent.concl p) in
   let f, _ = dest_apply app in
   let f_type =
      try get_with_arg p with
         RefineError _ ->
            infer_type p f
   in
   let univ =
      if is_dfun_term f_type then
         let _, _, univ = dest_dfun f_type in
            univ
      else if is_fun_term f_type then
         snd (dest_fun f_type)
      else
         raise (RefineError ("d_apply_typeT", StringTermError ("inferred type is not a function type", f_type)))
   in
      if is_univ_term univ then
         (univTypeT univ thenT withT f_type eqcdT) p
      else
         raise (RefineError ("d_apply_typeT", StringTermError ("inferred type is not a univ", univ)))

let apply_type_term = << "type"{. 'f 'a} >>

let resource intro += [
   apply_equal_term, wrap_intro d_apply_equalT;
   apply_type_term, wrap_intro d_apply_typeT
]

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_fun i p =
   let f = Sequent.nth_binding p i in
   let i, j = Sequent.hyp_indices p i in
   let y, z = maybe_new_vars2 p "y" "z" in
      try
         let a = get_with_arg p in
            independentFunctionElimination2 i j f y z a p
      with
         RefineError _ ->
            independentFunctionElimination i j f y p

let resource elim += (fun_term, d_hyp_fun)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let resource typeinf += (fun_term, infer_univ_dep0_dep0 dest_fun)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let fun_subtypeT p =
   independentFunctionSubtype (Sequent.hyp_count_addr p) p

let resource sub +=
   (DSubtype ([<< 'A1 -> 'B1 >>, << 'A2 -> 'B2 >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1 >>, << 'B2 >>],
              fun_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
