(*
 * Simplifications for undependent functions.
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
 *
 *)

include Tacticals

include Itt_equal
include Itt_dfun

open Printf
open Nl_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Nl_resource

open Sequent
open Tacticals
open Var

open Typeinf

open Itt_equal
open Itt_subtype
open Itt_rfun
open Itt_dfun

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_fun%t" eflush

(* debug_string DebugLoad "Loading itt_fun..." *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw reduceIndependentEta ('A -> 'B) : ('f = 'f in 'A -> 'B) -->
   lambda{x. 'f 'x} <--> 'f

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext A -> B
 * by independentFunctionFormation
 *
 * H >- Ui ext A
 * H >- Ui ext B
 *)
prim independentFunctionFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[@i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   'A -> 'B

(*
 * H >- (A1 -> B1) = (A2 -> B2) in Ui
 * by independentFunctionEquality
 *
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
prim independentFunctionEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- ('A1 -> 'B1) = ('A2 -> 'B2) in univ[@i:l] } =
   it

(*
 * Typehood.
 *)
prim independentFunctionType 'H 'x :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H; x: 'A1 >- "type"{'B1} } -->
   sequent ['ext] { 'H >- "type"{. 'A1 -> 'B1 } } =
   it

(*
 * H >- a:A -> B[a] ext lambda(z. b[z])
 * by lambdaFormation Ui z
 *
 * H >- A = A in Ui
 * H, z: A >- B[z] ext b[z]
 *)
prim independentLambdaFormation 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   ('b['z] : sequent ['ext] { 'H; z: 'A >- 'B }) -->
   sequent ['ext] { 'H >- 'A -> 'B } =
   lambda{z. 'b['z]}

(*
 * H >- lambda(a1. b1[a1]) = lambda(a2. b2[a2]) in a:A -> B
 * by lambdaEquality Ui x
 *
 * H >- A = A in Ui
 * H, x: A >- b1[x] = b2[x] in B[x]
 *)
prim independentLambdaEquality 'H 'x :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'A >- 'b1['x] = 'b2['x] in 'B } -->
   sequent ['ext] { 'H >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in 'A -> 'B } =
   it

(*
 * H, f: A -> B, J[x] >- T[x]                   ext t[f, f a]
 * by independentFunctionElimination i y
 *
 * H, f: A -> B, J >- A                         ext a
 * H, f: A -> B, J[x], y: B >- T[x]             ext t[f, y]
 *)
prim independentFunctionElimination 'H 'J 'f 'y :
   ('a : sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'A }) -->
   ('t['f; 'y] : sequent ['ext] { 'H; f: 'A -> 'B; 'J['f]; y: 'B >- 'T['f] }) -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'T['f] } =
   't['f; 'f 'a]

(*
 * Explicit function elimination.
 *)
prim independentFunctionElimination2 'H 'J 'f 'y 'z 'a :
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'a = 'a in 'A } -->
   ('t['y; 'z] : sequent ['ext] { 'H; f: 'A -> 'B; 'J['f]; y: 'B; z: 'y = ('f 'a) in 'B >- 'T['f] }) -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'T['f] } =
   't['f 'a; it]

(*
 * H >- (f1 a1) = (f2 a2) in B[a1]
 * by applyEquality (x:A -> B[x])
 *
 * H >- f1 = f2 in x:A -> B[x]
 * H >- a1 = a2 in A
 *)
prim independentApplyEquality 'H ('A -> 'B) :
   sequent [squash] { 'H >- 'f1 = 'f2 in 'A -> 'B } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- ('f1 'a1) = ('f2 'a2) in 'B } =
   it

(*
 * H >- A1 -> B1 <= A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H >- B1 <= B2
 *)
prim independentFunctionSubtype 'H :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 -> 'B1); ('A2 -> 'B2) } } =
   it

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_fun p =
   let count = hyp_count_addr p in
   let z = get_opt_var_arg "z" p in
      (independentLambdaFormation count z
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "main"]) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_fun i p =
   let f, _ = Sequent.nth_hyp p i in
   let i, j = hyp_indices p i in
   let y, z = maybe_new_vars2 p "y" "z" in
      try
         let a = get_with_arg p in
            (independentFunctionElimination2 i j f y z a
             thenLT [addHiddenLabelT "wf";
                     addHiddenLabelT "main"]) p
      with
         RefineError _ ->
            (independentFunctionElimination i j f y
             thenLT [addHiddenLabelT "antecedent";
                     addHiddenLabelT "main"]) p

(*
 * Join them.
 *)
let d_funT i =
   if i = 0 then
      d_concl_fun
   else
      d_hyp_fun i

let d_resource = d_resource.resource_improve d_resource (fun_term, d_funT)

(*
 * Typehood.
 *)
let d_fun_typeT i p =
   if i = 0 then
      let x = maybe_new_vars1 p "x" in
         independentFunctionType (hyp_count_addr p) x p
   else
      let _, t = Sequent.nth_hyp p i in
         raise (RefineError ("d_fun_typeT", StringTermError ("no elimination form", t)))

let fun_type_term = << "type"{. 'A -> 'B } >>

let d_resource = d_resource.resource_improve d_resource (fun_type_term, d_fun_typeT)

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

(*
 * EQCD.
 *)
let eqcd_funT p =
   let count = hyp_count_addr p in
      (independentFunctionEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (fun_term, eqcd_funT)

let fun_equal_term = << ('A1 -> 'A2) = ('B1 -> 'B2) in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (fun_equal_term, d_wrap_eqcd eqcd_funT)

(*
 * Apply equality.
 *)
let eqcd_applyT p =
   let t =
      try get_with_arg p with
         RefineError _ ->
            let eq_type, app, _ = dest_equal (Sequent.concl p) in
            let f, a = dest_apply app in
               try snd (infer_type p f) with
                  RefineError _ ->
                     let _, arg_type = infer_type p a in
                        mk_fun_term arg_type eq_type
   in
   let i = hyp_count_addr p in
      if is_fun_term t then
         independentApplyEquality i t p
      else if is_dfun_term t then
         applyEquality i t p
      else
         raise (RefineError ("eqcd_applyT", StringTermError ("argument should be a function type", t)))

let apply_equal_term = << ('f1 'a1) = ('f2 'a2) in 'T >>

let d_resource = d_resource.resource_improve d_resource (apply_equal_term, d_wrap_eqcd eqcd_applyT)

(*
 * Typehood of application depends on the ability to infer a type.
 *)
let d_apply_typeT i p =
   if i = 0 then
      let app = dest_type_term (Sequent.concl p) in
      let f, _ = dest_apply app in
      let f_type =
         try get_with_arg p with
            RefineError _ ->
               snd (infer_type p f)
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
            (univTypeT univ thenT withT f_type eqcd_applyT) p
         else
            raise (RefineError ("d_apply_typeT", StringTermError ("inferred type is not a univ", univ)))
   else
      raise (RefineError ("d_apply_typeT", StringError "no elimination form"))

let apply_type_term = << "type"{. 'f 'a} >>

let d_resource = d_resource.resource_improve d_resource (apply_type_term, d_apply_typeT)

(*
 * Lambda equality.
 *)
let eqcd_lambdaT p =
   let t, l, _ = dest_equal (concl p) in
   let v, _ = dest_lambda l in
   let x = get_opt_var_arg v p in
   let count = hyp_count_addr p in
   let tac =
      if is_fun_term t then
         independentLambdaEquality count x
      else if is_dfun_term t then
         lambdaEquality count x
      else
         raise (RefineError ("eqcd_lambdaT", StringTermError ("type is not a function tye", t)))
   in
      (tac thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (lambda_term, eqcd_lambdaT)

let lambda_equal_term = << lambda{x1. 'b1['x1]} = lambda{x2. 'b2['x2]} in x3: 'A -> 'B['x3] >>

let d_resource = d_resource.resource_improve d_resource (lambda_equal_term, d_wrap_eqcd eqcd_lambdaT)

let lambda_equal_term = << lambda{x1. 'b1['x1]} = lambda{x2. 'b2['x2]} in 'A -> 'B >>

let d_resource = d_resource.resource_improve d_resource (lambda_equal_term, d_wrap_eqcd eqcd_lambdaT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_fun f decl t =
   let a, b = dest_fun t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (fun_term, inf_fun)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let fun_subtypeT p =
   (independentFunctionSubtype (hyp_count_addr p)
    thenT addHiddenLabelT "subtype") p

let sub_resource =
   sub_resource.resource_improve
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
