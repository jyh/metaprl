(*
 * Dependent functions.
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

include Var

include Itt_equal
include Itt_rfun

open Printf
open Nl_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Nl_resource

open Var
open Sequent
open Tacticals
open Itt_equal
open Itt_subtype
open Itt_rfun

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_dfun%t" eflush


(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw reduceEta (x: 'A -> 'B['x]) : ('f = 'f in (x: 'A -> 'B['x])) -->
   lambda{x. 'f 'x} <--> 'f

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext a:A -> B
 * by functionFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
prim functionFormation 'H 'a 'A :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   ('B['a] : sequent ['ext] { 'H; a: 'A >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   a:'A -> 'B

(*
 * H >- (a1:A1 -> B1[a1]) = (a2:A2 -> B2[a2]) in Ui
 * by functionEquality x
 *
 * H >- A1 = A2 in Ui
 * H, x: A1 >- B1[x] = B2[x] in Ui
 *)
prim functionEquality 'H 'x :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[@i:l] } -->
   sequent ['ext] { 'H >- (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[@i:l] } =
   it

(*
 * Typehood.
 *)
prim functionType 'H 'x :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H; x: 'A1 >- "type"{'B1['x]} } -->
   sequent ['ext] { 'H >- "type"{. a1:'A1 -> 'B1['a1] } } =
   it

(*
 * H >- a:A -> B[a] ext lambda(z. b[z])
 * by lambdaFormation Ui z
 *
 * H >- A = A in Ui
 * H, z: A >- B[z] ext b[z]
 *)
prim lambdaFormation 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   ('b['z] : sequent ['ext] { 'H; z: 'A >- 'B['z] }) -->
   sequent ['ext] { 'H >- a:'A -> 'B['a] } =
   lambda{z. 'b['z]}

(*
 * H >- lambda(a1. b1[a1]) = lambda(a2. b2[a2]) in a:A -> B
 * by lambdaEquality Ui x
 *
 * H >- A = A in Ui
 * H, x: A >- b1[x] = b2[x] in B[x]
 *)
prim lambdaEquality 'H 'x :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'A >- 'b1['x] = 'b2['x] in 'B['x] } -->
   sequent ['ext] { 'H >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in a:'A -> 'B['a] } =
   it

(*
 * H >- f = g in x:A -> B
 * by functionExtensionality Ui (y:C -> D) (z:E -> F) u
 *
 * H, u:A >- f(u) = g(u) in B[u]
 * H >- A = A in Ui
 * H >- f = f in y:C -> D
 * H >- g = g in z:E -> F
 *)
prim functionExtensionality 'H (y:'C -> 'D['y]) (z:'E -> 'F['z]) 'u :
   sequent [squash] { 'H; u: 'A >- ('f 'u) = ('g 'u) in 'B['u] } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- 'f = 'f in y:'C -> 'D['y] } -->
   sequent [squash] { 'H >- 'g = 'g in z:'E -> 'F['z] } -->
   sequent ['ext] { 'H >- 'f = 'g in x:'A -> 'B['x] } =
   it

(*
 * H, f: (x:A -> B), J[x] >- T[x] t[f, f a, it]
 * by functionElimination i a y v
 *
 * H, f: (x:A -> B), J[x] >- a = a in A
 * H, f: (x:A -> B), J[x], y: B[a], v: y = f(a) in B[a] >- T[x] ext t[f, y, v]
 *)
prim functionElimination 'H 'J 'f 'a 'y 'v :
   sequent [squash] { 'H; f: x:'A -> 'B['x]; 'J['f] >- 'a = 'a in 'A } -->
   ('t['f; 'y; 'v] : sequent ['ext] { 'H; f: x:'A -> 'B['x]; 'J['f]; y: 'B['a]; v: 'y = ('f 'a) in 'B['a] >- 'T['f] }) -->
   sequent ['ext] { 'H; f: x:'A -> 'B['x]; 'J['f] >- 'T['f] } =
   't['f; 'f 'a; it]

(*
 * H >- (f1 a1) = (f2 a2) in B[a1]
 * by applyEquality (x:A -> B[x])
 *
 * H >- f1 = f2 in x:A -> B[x]
 * H >- a1 = a2 in A
 *)
prim applyEquality 'H (x:'A -> 'B['x]) :
   sequent [squash] { 'H >- 'f1 = 'f2 in x:'A -> 'B['x] } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- ('f1 'a1) = ('f2 'a2) in 'B['a1] } =
   it

(*
 * H >- a1:A1 -> B1 <= a2:A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H, a: A1 >- B1[a] <= B2[a]
 *)
prim functionSubtype 'H 'a :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['prop] { 'H >- subtype{ (a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2]) } } =
   it

(*
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; J[x] >- T[x]
 * by function_subtypeElimination i
 *
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; y: A2 <= A1; z: a:A2 -> B2[a] <= B1[a]; J[x] >- T[x]
 *)
prim function_subtypeElimination 'H 'J 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent { 'H;
             x: subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])};
             'J['x];
             y: subtype{'A2; 'A1};
             z: a:'A2 -> subtype{'B1['a]; 'B2['a]}
             >- 'T['x]
           }) -->
   sequent { 'H; x: subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])}; 'J['x] >- 'T['x] } =
   't['x; it; lambda{x. it}]

(*
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; J[x] >- T[x]
 * by function_equalityElimination
 *
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; y: A1 = A2 in Ui; z: a:A1 -> B1[a] = B2[a] in Ui; J[x] >- T[x]
 *)
prim function_equalityElimination 'H 'J 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent { 'H;
             x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[@i:l];
             'J['x];
             y: 'A1 = 'A2 in univ[@i:l];
             z: a:'A1 -> ('B1['a] = 'B2['a] in univ[@i:l])
             >- 'T['x]
           }) -->
   sequent { 'H; x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[@i:l]; 'J['x] >- 'T['x] } =
   't['x; it; lambda{x. it}]

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_dfun p =
   let count = hyp_count_addr p in
   let t = concl p in
   let z, _, _ = dest_dfun t in
   let z' = get_opt_var_arg z p in
      (lambdaFormation count z'
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "main"]) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_dfun i p =
   let a =
      try get_with_arg p with
         Not_found ->
            raise (RefineError ("d_hyp_dfun", StringError "requires an argument"))
   in
   let f, _ = Sequent.nth_hyp p i in
   let i, j = hyp_indices p i in
   let y, v = maybe_new_vars2 p "y" "v" in
       (functionElimination i j f a y v
        thenLT [addHiddenLabelT "wf";
                addHiddenLabelT "main"]) p

(*
 * Join them.
 *)
let d_dfunT i =
   if i = 0 then
      d_concl_dfun
   else
      d_hyp_dfun i

let d_resource = d_resource.resource_improve d_resource (dfun_term, d_dfunT)

(*
 * Typehood.
 *)
let d_dfun_typeT i p =
   if i = 0 then
      let x = maybe_new_vars1 p "x" in
         functionType (hyp_count_addr p) x p
   else
      let _, t = Sequent.nth_hyp p i in
         raise (RefineError ("d_dfun_typeT", StringTermError ("no elimination form", t)))

let dfun_type_term = << "type"{. x:'A -> 'B['x] } >>

let d_resource = d_resource.resource_improve d_resource (dfun_type_term, d_dfun_typeT)

(************************************************************************
 * EQCD TACTICS                                                         *
 ************************************************************************)

(*
 * EQCD dfun.
 *)
let eqcd_dfunT p =
   let _, x, _ = dest_equal (concl p) in
   let v, _, _ = dest_dfun x in
   let x = get_opt_var_arg v p in
   let count = hyp_count_addr p in
      (functionEquality count x
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (dfun_term, eqcd_dfunT)

let dfun_equal_term = << (x1 : 'A1 -> 'B1['x1]) = (x2 : 'A2 -> 'B2['x2]) in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (dfun_equal_term, d_wrap_eqcd eqcd_dfunT)

(*
 * Save this for itt_fun.
(*
 * EQCD lambda.
 *)
let eqcd_lambdaT p =
   let _, l, _ = dest_equal (concl p) in
   let v, _ = dest_lambda l in
   let x = get_opt_var_arg v p in
   let count = hyp_count_addr p in
      (lambdaEquality count x
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (lambda_term, eqcd_lambdaT)

let lambda_equal_term = << lambda{x1. 'b1['x1]} = lambda{x2. 'b2['x2]} in x3: 'A -> 'B['x3] >>

let d_resource = d_resource.resource_improve d_resource (lambda_equal_term, d_wrap_eqcd eqcd_lambdaT)
*)

(*
 * Leave this for itt_fun.
(*
 * EQCD apply.
 *)
let eqcd_applyT p =
   let t =
      try get_with_arg p with
         RefineError _ ->
            raise (RefineError ("eqcd_applyT", StringError "need an argument"))
   in
   let count = hyp_count_addr p in
      (applyEquality count t
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (apply_term, eqcd_applyT)

let apply_equal_term = << ('f1 'x1) = ('f2 'x2) in 'B >>

let d_resource = d_resource.resource_improve d_resource (apply_equal_term, d_wrap_eqcd eqcd_applyT)
*)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_dfun f decl t =
   let v, a, b = dest_dfun t in
   let decl', a' = f decl a in
   let decl'', b' = f (add_unify_subst v a decl') b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (dfun_term, inf_dfun)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let dfun_subtypeT p =
   let a = get_opt_var_arg "x" p in
      (functionSubtype (hyp_count_addr p) a
       thenT addHiddenLabelT "subtype") p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (DSubtype ([<< a1:'A1 -> 'B1['a1] >>, << a2:'A2 -> 'B2['a2] >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              dfun_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
