(*
 * Dependent functions.
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

include Var

include Itt_equal
include Itt_rfun
include Itt_struct
include Itt_void
include Itt_unit

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_dtactic

open Itt_equal
open Itt_subtype
open Itt_rfun
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_dfun%t"


(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw reduceEta (x: 'A -> 'B['x]) : ('f = 'f in (x: 'A -> 'B['x])) -->
   lambda{x. 'f 'x} <--> 'f

prim_rw unfold_dfun : (x: 'A -> 'B['x]) <--> ({ f | x: 'A -> 'B['x] })

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Use the discrete ordering.
 *)
interactive void_well_founded {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- well_founded{'A; a1, a2. void} }

(*
 * H >- (a1:A1 -> B1[a1]) = (a2:A2 -> B2[a2]) in Ui
 * by functionEquality x
 *
 * H >- A1 = A2 in Ui
 * H, x: A1 >- B1[x] = B2[x] in Ui
 *)
interactive functionEquality {| intro_resource []; eqcd_resource |} 'H 'x :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[i:l] } -->
   sequent ['ext] { 'H >- (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l] }

interactive functionMember {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'A1} } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- member{univ[i:l]; 'B1['x]} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; .a1:'A1 -> 'B1['a1]} }

(*
 * Typehood.
 *)
interactive functionType {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A1} } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- "type"{'B1['x]} } -->
   sequent ['ext] { 'H >- "type"{. a1:'A1 -> 'B1['a1] } }

(*
 * H >- a:A -> B[a] ext lambda(z. b[z])
 * by lambdaFormation Ui z
 *
 * H >- A = A in Ui
 * H, z: A >- B[z] ext b[z]
 *)
interactive lambdaFormation {| intro_resource [] |} 'H 'z :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [main] ('b['z] : sequent ['ext] { 'H; z: 'A >- 'B['z] }) -->
   sequent ['ext] { 'H >- a:'A -> 'B['a] }

(*
 * H >- lambda(a1. b1[a1]) = lambda(a2. b2[a2]) in a:A -> B
 * by lambdaEquality Ui x
 *
 * H >- A = A in Ui
 * H, x: A >- b1[x] = b2[x] in B[x]
 *)
interactive lambdaEquality {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; x: 'A >- 'b1['x] = 'b2['x] in 'B['x] } -->
   sequent ['ext] { 'H >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in a:'A -> 'B['a] }

interactive lambdaMember {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; x: 'A >- member{'B['x]; 'b1['x]} } -->
   sequent ['ext] { 'H >- member{.a:'A -> 'B['a]; lambda{a1. 'b1['a1]}} }

(*
 * H >- f = g in x:A -> B
 * by functionExtensionality Ui (y:C -> D) (z:E -> F) u
 *
 * H, u:A >- f(u) = g(u) in B[u]
 * H >- A = A in Ui
 * H >- f = f in y:C -> D
 * H >- g = g in z:E -> F
 *)
interactive functionExtensionality 'H (y:'C -> 'D['y]) (z:'E -> 'F['z]) 'u :
   [main] sequent [squash] { 'H; u: 'A >- ('f 'u) = ('g 'u) in 'B['u] } -->
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- 'f = 'f in y:'C -> 'D['y] } -->
   [wf] sequent [squash] { 'H >- 'g = 'g in z:'E -> 'F['z] } -->
   sequent ['ext] { 'H >- 'f = 'g in x:'A -> 'B['x] }

interactive functionExtensionalityMember 'H (y:'C -> 'D['y]) 'u :
   [main] sequent [squash] { 'H; u: 'A >- member{'B['u]; .'f 'u} } -->
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- member{.y:'C -> 'D['y]; 'f} } -->
   sequent ['ext] { 'H >- member{.x:'A -> 'B['x]; 'f} }

(*
 * H, f: (x:A -> B), J[x] >- T[x] t[f, f a, it]
 * by functionElimination i a y v
 *
 * H, f: (x:A -> B), J[x] >- a = a in A
 * H, f: (x:A -> B), J[x], y: B[a], v: y = f(a) in B[a] >- T[x] ext t[f, y, v]
 *)
interactive functionElimination {| elim_resource [] |} 'H 'J 'f 'a 'y 'v :
   [wf] sequent [squash] { 'H; f: x:'A -> 'B['x]; 'J['f] >- member{'A; 'a} } -->
   ('t['f; 'y; 'v] : sequent ['ext] { 'H; f: x:'A -> 'B['x]; 'J['f]; y: 'B['a]; v: 'y = ('f 'a) in 'B['a] >- 'T['f] }) -->
   sequent ['ext] { 'H; f: x:'A -> 'B['x]; 'J['f] >- 'T['f] }

(*
 * H >- (f1 a1) = (f2 a2) in B[a1]
 * by applyEquality (x:A -> B[x])
 *
 * H >- f1 = f2 in x:A -> B[x]
 * H >- a1 = a2 in A
 *)
interactive applyEquality {| eqcd_resource |} 'H (x:'A -> 'B['x]) :
   sequent [squash] { 'H >- 'f1 = 'f2 in x:'A -> 'B['x] } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- ('f1 'a1) = ('f2 'a2) in 'B['a1] }

interactive applyMember 'H (x:'A -> 'B['x]) :
   sequent [squash] { 'H >- member{. x:'A -> 'B['x]; 'f1} } -->
   sequent [squash] { 'H >- member{'A; 'a1} } -->
   sequent ['ext] { 'H >- member{'B['a1]; .'f1 'a1} }

(*
 * H >- a1:A1 -> B1 <= a2:A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H, a: A1 >- B1[a] <= B2[a]
*)
interactive functionSubtype {| intro_resource [] |} 'H 'a :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['prop] { 'H >- subtype{ (a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2]) } }

(*
(*
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; J[x] >- T[x]
 * by function_subtypeElimination i
 *
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; y: A2 <= A1; z: a:A2 -> B2[a] <= B1[a]; J[x] >- T[x]
 *)
interactive function_subtypeElimination {| elim_resource [] |} 'H 'J 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent ['ext] { 'H;
             x: subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])};
             'J['x];
             y: subtype{'A2; 'A1};
             z: a:'A2 -> subtype{'B1['a]; 'B2['a]}
             >- 'T['x]
           }) -->
   sequent ['ext] { 'H; x: subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])}; 'J['x] >- 'T['x] }
*)

(*
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; J[x] >- T[x]
 * by function_equalityElimination
 *
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; y: A1 = A2 in Ui; z: a:A1 -> B1[a] = B2[a] in Ui; J[x] >- T[x]
interactive function_equalityElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent { 'H;
             x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l];
             'J['x];
             y: 'A1 = 'A2 in univ[i:l];
             z: a:'A1 -> ('B1['a] = 'B2['a] in univ[i:l])
             >- 'T['x]
           }) -->
   sequent { 'H; x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l]; 'J['x] >- 'T['x] }
 *)

(*
 * H >- Ui ext a:A -> B
 * by functionFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
interactive functionFormation 'H 'a 'A :
   [wf] sequent [squash] { 'H >- 'A = 'A in univ[i:l] } -->
   ('B['a] : sequent ['ext] { 'H; a: 'A >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] }

(************************************************************************
 * EXTENSIOANLITY                                                       *
 ************************************************************************)

(*
 * Takes two arguments.
 *)
let dfun_extensionalityT t1 t2 p =
   let t, _, _ = dest_equal (Sequent.concl p) in
   let v, _, _ = dest_dfun t in
   let v = maybe_new_vars1 p v in
      functionExtensionality (Sequent.hyp_count_addr p) t1 t2 v p

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
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2 0)

let typeinf_resource = Mp_resource.improve typeinf_resource (dfun_term, inf_dfun)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let dfun_subtypeT p =
   let a = get_opt_var_arg "x" p in
      (functionSubtype (Sequent.hyp_count_addr p) a
       thenT addHiddenLabelT "subtype") p

let sub_resource =
   Mp_resource.improve
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
