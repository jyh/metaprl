(*
 * Simplifications for undependent functions.
 *
 * ----------------------------------------------------------------
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
 * jyh@cs.cornell.edu
 *
 *)

include Itt_equal
include Itt_dfun

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

prim_rw reduceIndependentEta ('A -> 'B) : ('f = 'f in 'A -> 'B) -->
   lambda{x. 'f 'x} <--> 'f

prim_rw unfold_fun : ('A -> 'B) <--> (x: 'A -> 'B)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- (A1 -> B1) = (A2 -> B2) in Ui
 * by independentFunctionEquality
 *
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
interactive independentFunctionEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- ('A1 -> 'B1) = ('A2 -> 'B2) in univ[i:l] }

(*
 * Typehood.
 *)
interactive independentFunctionType {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A1} } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- "type"{'B1} } -->
   sequent ['ext] { 'H >- "type"{. 'A1 -> 'B1 } }

(*
 * H >- a:A -> B[a] ext lambda(z. b[z])
 * by lambdaFormation Ui z
 *
 * H >- A = A in Ui
 * H, z: A >- B[z] ext b[z]
 *)
interactive independentLambdaFormation {| intro_resource [] |} 'H 'z :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [main] ('b['z] : sequent ['ext] { 'H; z: 'A >- 'B }) -->
   sequent ['ext] { 'H >- 'A -> 'B }

(*
 * H >- lambda(a1. b1[a1]) = lambda(a2. b2[a2]) in a:A -> B
 * by lambdaEquality Ui x
 *
 * H >- A = A in Ui
 * H, x: A >- b1[x] = b2[x] in B[x]
 *)
interactive independentLambdaEquality {| intro_resource []; eqcd_resource |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; x: 'A >- 'b1['x] = 'b2['x] in 'B } -->
   sequent ['ext] { 'H >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in 'A -> 'B }

(*
 * H, f: A -> B, J[x] >- T[x]                   ext t[f, f a]
 * by independentFunctionElimination i y
 *
 * H, f: A -> B, J >- A                         ext a
 * H, f: A -> B, J[x], y: B >- T[x]             ext t[f, y]
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

(*
 * H >- (f1 a1) = (f2 a2) in B[a1]
 * by applyEquality (x:A -> B[x])
 *
 * H >- f1 = f2 in x:A -> B[x]
 * H >- a1 = a2 in A
 *)
interactive independentApplyEquality {| eqcd_resource |} 'H ('A -> 'B) :
   [wf] sequent [squash] { 'H >- 'f1 = 'f2 in 'A -> 'B } -->
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- ('f1 'a1) = ('f2 'a2) in 'B }

(*
 * H >- A1 -> B1 <= A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H >- B1 <= B2
 *)
interactive independentFunctionSubtype 'H :
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

let intro_resource = Mp_resource.improve intro_resource (apply_equal_term, d_apply_equalT)

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

let intro_resource = Mp_resource.improve intro_resource (apply_type_term, d_apply_typeT)

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_fun i p =
   let f, _ = Sequent.nth_hyp p i in
   let i, j = Sequent.hyp_indices p i in
   let y, z = maybe_new_vars2 p "y" "z" in
      try
         let a = get_with_arg p in
            independentFunctionElimination2 i j f y z a p
      with
         RefineError _ ->
            independentFunctionElimination i j f y p

let elim_resource = Mp_resource.improve elim_resource (fun_term, d_hyp_fun)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let typeinf_resource =
   Mp_resource.improve typeinf_resource (fun_term, infer_univ_dep0_dep0 dest_fun)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let fun_subtypeT p =
   independentFunctionSubtype (Sequent.hyp_count_addr p) p

let sub_resource =
   Mp_resource.improve
   sub_resource
   (DSubtype ([<< 'A1 -> 'B1 >>, << 'A2 -> 'B2 >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1 >>, << 'B2 >>],
              fun_subtypeT))

(************************************************************************
 * CONVERSIONAL                                                         *
 ************************************************************************)

let etaC t =
   if is_fun_term t then
      reduceIndependentEta t
   else if is_dfun_term t then
      Itt_dfun.reduceEta t
   else
      raise (RefineError ("etaC", StringTermError ("argument is not a function type", t)))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
