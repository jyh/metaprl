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
 * jyhcs.cornell.edu
 *
 *)

include Itt_equal
include Itt_void
include Itt_set
include Itt_struct

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
open Typeinf
open Base_dtactic

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent

open Itt_void
open Itt_equal
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_rfun%t"

(* debug_string DebugLoad "Loading itt_rfun..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(* declare "fun"{'A; 'B} *)
declare "fun"{'A; x. 'B['x]}
declare rfun{'A; f, x. 'B['f; 'x]}

declare lambda{x. 'b['x]}
declare apply{'f; 'a}

declare well_founded{'A; x, y. 'R['x; 'y]}
declare well_founded_assum{'A; a1, a2. 'R['a1; 'a2]; 'P}
declare well_founded_prop{'A}
declare well_founded_apply{'P; 'a}
declare fix{f. 'b['f]}

(*
 * Primitives.
 *)
let rfun_term = << { f | x: 'A -> 'B['f; 'x] } >>
let rfun_opname = opname_of_term rfun_term
let is_rfun_term = is_dep0_dep2_term rfun_opname
let dest_rfun = dest_dep0_dep2_term rfun_opname
let mk_rfun_term = mk_dep0_dep2_term rfun_opname

let well_founded_term = << well_founded{'A; x, y. 'R['x; 'y]} >>
let well_founded_opname = opname_of_term well_founded_term
let is_well_founded_term = is_dep0_dep2_term well_founded_opname
let dest_well_founded = dest_dep0_dep2_term well_founded_opname
let mk_well_founded_term = mk_dep0_dep2_term well_founded_opname

let lambda_term = << lambda{x. 'b['x]} >>
let lambda_opname = opname_of_term lambda_term
let is_lambda_term = is_dep1_term lambda_opname
let dest_lambda = dest_dep1_term lambda_opname
let mk_lambda_term = mk_dep1_term lambda_opname

let fix_term = << fix{x. 'b['x]} >>
let fix_opname = opname_of_term fix_term
let is_fix_term = is_dep1_term fix_opname
let dest_fix = dest_dep1_term fix_opname
let mk_fix_term = mk_dep1_term fix_opname

let apply_term = << apply{'f; 'a} >>
let apply_opname = opname_of_term apply_term
let is_apply_term = is_dep0_dep0_term apply_opname
let dest_apply = dest_dep0_dep0_term apply_opname
let mk_apply_term = mk_dep0_dep0_term apply_opname

let dfun_term = << x: 'A -> 'B['x] >>
let dfun_opname = opname_of_term dfun_term
let is_dfun_term = is_dep0_dep1_term dfun_opname
let dest_dfun = dest_dep0_dep1_term dfun_opname
let mk_dfun_term = mk_dep0_dep1_term dfun_opname

let fun_term = << 'A -> 'B >>
let fun_opname = opname_of_term fun_term
let is_fun_term = is_dep0_dep0_term fun_opname
let dest_fun = dest_dep0_dep0_term fun_opname
let mk_fun_term = mk_dep0_dep0_term fun_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_fun
prec prec_apply
prec prec_lambda
prec prec_lambda < prec_apply
prec prec_fun < prec_apply
prec prec_fun < prec_lambda

dform fun_df1 : parens :: "prec"[prec_fun] :: "fun"{'A; 'B} =
   slot["le"]{'A} " " rightarrow " " slot["lt"]{'B}

dform fun_df2 : parens :: "prec"[prec_fun] :: "fun"{'A; x. 'B} =
   slot{bvar{'x}} `":" slot{'A} " " rightarrow " " slot{'B}

dform fun_df3 : rfun{'A; f, x. 'B} =
   "{" " " slot{bvar{'f}} `" | "  "fun"{'A; x. 'B} `" }"

dform apply_df1 : parens :: "prec"[prec_apply] :: apply{'f; 'a} =
   slot["lt"]{'f} " " slot["le"]{'a}

dform lambda_df1 : parens :: "prec"[prec_lambda] :: lambda{x. 'b} =
   Nuprl_font!lambda slot{'x} `"." slot{'b}

dform fix_df1 : fix{f. 'b} =
   `"fix" "(" slot{'f} `"." slot{'b} ")"

dform well_founded_prop_df : well_founded_prop{'A} =
   `"WellFounded " slot{'A} " " rightarrow `" Prop"

dform well_founded_apply_df : well_founded_apply{'P; 'a} =
   slot{'P} `"[" slot{'a} `"]"

dform well_founded_assum_df : well_founded_assum{'A; a1, a2. 'R; 'P} =
   szone pushm[3] `"WellFounded " Nuprl_font!forall slot{'a2} `":" slot{'A} `"."
   `"(" Nuprl_font!forall slot{'a1} `":" slot{'A} `". " slot{'R} " " Rightarrow well_founded_apply{'P; 'a1} `")"
   Rightarrow well_founded_apply{'P; 'a2} popm ezone

dform well_founded_df : well_founded{'A; a, b. 'R} =
   szone pushm[3] `"WellFounded " slot{'a} `"," slot{'b} `":" slot{'A} `"." slot{'R} popm ezone

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * apply(lambda(v. b[v]); a) -> b[a]
 *)
prim_rw reduce_beta : (lambda{v. 'b['v]} 'a) <--> 'b['a]
prim_rw reduce_fix : fix{f. 'b['f]} <--> 'b[fix{f. 'b['f]}]

let reduce_info =
   [<< (lambda{v. 'b['v]} 'a) >>, reduce_beta;
    << fix{f. 'b['f]} >>, reduce_fix]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Well-founded means that there is an induction principle.
 *)
prim well_founded_assum_elim {| elim_resource [ThinOption thinT] |} 'H 'J 'a 'a3 'u :
   [main] sequent [squash] { 'H; p: well_founded_assum{'A; a1, a2. 'R['a1; 'a2]; 'P}; 'J['p] >- member{'A; 'a} } -->
   [main] sequent [squash] { 'H; p: well_founded_assum{'A; a1, a2. 'R['a1; 'a2]; 'P}; 'J['p]; a3: 'A; u: 'R['a3; 'a] >- well_founded_apply{'P; 'a3} } -->
   [main] ('t['u] : sequent [squash] { 'H; p: well_founded_assum{'A; a1, a2. 'R['a1; 'a2]; 'P}; 'J['p]; u: well_founded_apply{'P; 'a} >- 'C['p] }) -->
   sequent ['ext] { 'H; p: well_founded_assum{'A; a1, a2. 'R['a1; 'a2]; 'P}; 'J['p] >- 'C['p] } =
   't[it]

prim well_founded {| intro_resource [] |} 'H 'a1 'a2 'a3 'u 'v 'p 'P :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; a1: 'A; a2: 'A >- "type"{'R['a1; 'a2]} } -->
   [main] sequent [squash] { 'H; a1: 'A; u: 'R['a1; 'a1] >- void } -->
   [main] sequent [squash] { 'H; a1: 'A; a2: 'A; u: 'R['a1; 'a2]; v: 'R['a2; 'a1] >- void } -->
   [main] sequent [squash] { 'H; a1: 'A; a2: 'A; a3: 'A; u: 'R['a1; 'a2]; v: 'R['a2; 'a3] >- 'R['a1; 'a3] } -->
   [main] sequent [squash] { 'H; a1: 'A; P: well_founded_prop{'A}; p: well_founded_assum{'A; a2, a3. 'R['a2; 'a3]; 'P} >- well_founded_apply{'P; 'a1} } -->
   sequent ['ext] { 'H >- well_founded{'A; a, b. 'R['a; 'b]} } =
   it

prim well_founded_apply_type {| intro_resource [] |} 'H 'A :
   [wf] sequent [squash] { 'H >- member{well_founded_prop{'A}; 'P} } -->
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'A} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'a} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; well_founded_apply{'P; 'a}} } =
   it

(*
 * H >- Ui ext { f | a:A -> B }
 * by rfunctionFormation { f | a: A -> B }
 *
 * H >- { f | a: A -> B } = { f | a: A -> B } in Ui
 *)
prim rfunctionFormation 'H { f | a: 'A -> 'B['f; 'a] } :
   [wf] sequent [squash] { 'H >- { f | a: 'A -> 'B['f; 'a] } = { f | a: 'A -> 'B['f; 'a] } in univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] } =
   { f | a: 'A -> 'B['f; 'a] }

(*
 * H >- { f1 | a1:A1 -> B1[f1, a1] } = { f2 | a2:A2 -> B2[f2, a2] } in Ui
 * by rfunctionEquality R[a, b] g y z
 *
 * H >- A1 = A2 in Ui
 * H >- well_founded(A1; a, b. R[a, b])
 * H, y:A, g : { f1 | x1: { z: A1 | R z y } -> B1[f1, x1] } >- B1[g, y] = B2[g, y] in Ui
 *)
prim rfunctionEquality  {| intro_resource []; eqcd_resource |} 'H lambda{a. lambda{b. 'R['a; 'b]}} 'g 'y 'z :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- well_founded{'A1; a, b. 'R['a; 'b]} } -->
   [wf] sequent [squash] { 'H;
             y: 'A1;
             g: { f1 | x1: { z: 'A1 | 'R['z; 'y] } -> 'B1['f1; 'x1] }
             >- 'B1['g; 'y] = 'B2['g; 'y] in univ[i:l]
           } -->
   sequent ['ext] { 'H >- { f1 | a1:'A1 -> 'B1['f1; 'a1] }
                   = { f2 | a2:'A2 -> 'B2['f2; 'a2] }
                   in univ[i:l]
           } =
   it

interactive rfunctionMember  {| intro_resource [] |} 'H lambda{a. lambda{b. 'R['a; 'b]}} 'g 'y 'z :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'A1} } -->
   [wf] sequent [squash] { 'H >- well_founded{'A1; a, b. 'R['a; 'b]} } -->
   [wf] sequent [squash] { 'H;
             y: 'A1;
             g: { f1 | x1: { z: 'A1 | 'R['z; 'y] } -> 'B1['f1; 'x1] }
             >- member{univ[i:l]; 'B1['g; 'y]}
           } -->
   sequent ['ext] { 'H >- member{univ[i:l]; { f1 | a1:'A1 -> 'B1['f1; 'a1] }} }

prim rfunctionType  {| intro_resource [] |} 'H lambda{a. lambda{b. 'R['a; 'b]}} 'g 'y 'z :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- well_founded{'A; a, b. 'R['a; 'b]} } -->
   [wf] sequent [squash] { 'H;
             y: 'A;
             g: { f | x: { z: 'A | 'R['z; 'y] } -> 'B['f; 'x] }
             >- "type"{'B['g; 'y]}
           } -->
   sequent ['ext] { 'H >- "type"{. { f | a:'A -> 'B['f; 'a] } } } =
   it

(*
 * H >- { f | a:A -> B[a] } ext lambda(y. fix(g. b[g, y]))
 * by rfunctionLambdaFormation R[a, b] g y z
 *
 * H >- A = A in Ui
 * H >- well_founded(A; a, b. R[a, b])
 * H, y: A, g: { f | { z: A | R z y } -> B[f, x] } >- B[g, y] ext b[g, y]
 *)
prim rfunction_lambdaFormation {| intro_resource [] |} 'H lambda{a. lambda{b. 'R['a; 'b]}} 'g 'y 'z :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- well_founded{'A; a, b. 'R['a; 'b]} } -->
   ('b['g; 'y] : sequent ['ext] { 'H; y: 'A; g: { f | x: { z: 'A | 'R['z; 'y] } -> 'B['f; 'x] } >- 'B['g; 'y] }) -->
   sequent ['ext] { 'H >- { f | x:'A -> 'B['f; 'x] } } =
   lambda{y. fix{g. 'b['g; 'y]}}

(*
 * H >- lambda(x1. b1[x1]) = lambda(x2. b2[x2]) in {f | x:A -> B[f, x] }
 * by rfunction_lambdaEquality y
 *
 * H >- { f | x:A -> B[f, x] } = { f | x:A -> B[f, x] } in type
 * H, y: A >- b1[y] = b2[y] in B[lambda(x1. b1[x1]); y]
 *)
prim rfunction_lambdaEquality {| intro_resource []; eqcd_resource |} 'H 'y :
   [wf] sequent [squash] { 'H >- "type"{{ f | x: 'A -> 'B['f; 'x] }} } -->
   [wf] sequent [squash] { 'H; y: 'A >- 'b1['y] = 'b2['y] in 'B[lambda{x1. 'b1['x1]}; 'y] } -->
   sequent ['ext] { 'H >- lambda{x1. 'b1['x1]} = lambda{x2. 'b2['x2]} in { f | x: 'A -> 'B['f; 'x] } } =
   it

interactive rfunction_lambdaMember {| intro_resource [] |} 'H 'y :
   [wf] sequent [squash] { 'H >- "type"{{ f | x: 'A -> 'B['f; 'x] }} } -->
   [wf] sequent [squash] { 'H; y: 'A >- member{'B[lambda{x1. 'b1['x1]}; 'y]; 'b1['y]} } -->
   sequent ['ext] { 'H >- member{.{ f | x: 'A -> 'B['f; 'x] }; lambda{x1. 'b1['x1]}} }

(*
 * H >- f1 = f2 in { g | x:A -> B[g, x] }
 * by rfunctionExtensionality { g1 | x1:A1 -> B1[g1, x1] } { g2 | x2:A2 -> B2[g2, x2] } y
 *
 * H >- { g | x:A -> B[g, x] } = { g | x:A -> B[g, x] } in type
 * H, y: A >- f1 y = f2 y in B[f1, x]
 * H >- f1 = f1 in { g1 | x1:A1 -> B1[g1, x1] }
 * H >- f2 = f2 in { g2 | x2:A2 -> B2[g2, x2] }
 *)
prim rfunctionExtensionality 'H
        ({ g1 | x1:'A1 -> 'B1['g1; 'x1] })
        ({ g2 | x2:'A2 -> 'B2['g2; 'x2] })
        'y :
   [wf] sequent [squash] { 'H >- "type"{{ g | x:'A -> 'B['g; 'x] }} } -->
   [main] sequent [squash] { 'H; y: 'A >- 'f1 'y = 'f2 'y in 'B['f1; 'x] } -->
   [wf] sequent [squash] { 'H >- 'f1 = 'f1 in { g1 | x1:'A1 -> 'B1['g1; 'x1] } } -->
   [wf] sequent [squash] { 'H >- 'f2 = 'f2 in { g2 | x2:'A2 -> 'B2['g2; 'x2] } } -->
   sequent ['ext] { 'H >- 'f1 = 'f2 in { g | x:'A -> 'B['g; 'x] } } =
   it

interactive rfunctionExtensionalityMember 'H
        ({ g1 | x1:'A1 -> 'B1['g1; 'x1] })
        'y :
   [wf] sequent [squash] { 'H >- "type"{.{ g | x:'A -> 'B['g; 'x] }} } -->
   [main] sequent [squash] { 'H; y: 'A >- member{'B['f1; 'x]; .'f1 'y} } -->
   [wf] sequent [squash] { 'H >- member{.{ g1 | x1:'A1 -> 'B1['g1; 'x1] }; 'f1} } -->
   sequent ['ext] { 'H >- member{.{ g | x:'A -> 'B['g; 'x] }; 'f1} }

(*
 * H, f: { g | x:A -> B[g, x] }, J[f] >- T[f] ext t[f, f a, it]
 * by rfunctionElimination a y v
 *
 * H, f: { g | x:A -> B[g, x] }, J[f] >- a = a in A
 * H, f: { g | x:A -> B[g, x] }, J[f], y: B[f, a], v: y = f a in B[f, a] >- T[f] ext t[f, y, v]
 *)
prim rfunctionElimination {| elim_resource [] |} 'H 'J 'f 'a 'y 'v :
   [wf] sequent [squash] { 'H; f: { g | x:'A -> 'B['g; 'x] }; 'J['f] >- member{'A; 'a} } -->
   ('t['f; 'y; 'v] : sequent ['ext] { 'H;
                               f: { g | x:'A -> 'B['g; 'x] };
                               'J['f];
                               y: 'B['f; 'a];
                               v: 'y = 'f 'a in 'B['f; 'a]
                               >- 'T['f] }) -->
   sequent ['ext] { 'H; f: { g | x:'A -> 'B['g; 'x] }; 'J['f] >- 'T['f] } =
   't['f; 'f 'a; it]

(*
 * H >- f1 a1 = f2 a2 in B[f1, a1]
 * by rfunction_applyEquality { f | x:A -> B[f, x] }
 *
 * H >- f1 = f2 in { f | x:A -> B[f, x] }
 * H >- a1 = a2 in A
 *)
prim rfunction_applyEquality {| eqcd_resource |} 'H ({ f | x:'A -> 'B['f; 'x] }) :
   [wf] sequent [squash] { 'H >- 'f1 = 'f2 in { f | x:'A -> 'B['f; 'x] } } -->
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- 'f1 'a1 = 'f2 'a2 in 'B['f1; 'a1] } =
   it

let rfunction_applyEquality' t p =
   rfunction_applyEquality (Sequent.hyp_count_addr p) t p

interactive rfunction_applyMember 'H ({ f | x:'A -> 'B['f; 'x] }) :
   [wf] sequent [squash] { 'H >- member{.{ f | x:'A -> 'B['f; 'x] }; 'f1} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'a1} } -->
   sequent ['ext] { 'H >- member{.'B['f1; 'a1]; .'f1 'a1} }

let rfunction_applyMember' t p =
   rfunction_applyMember (Sequent.hyp_count_addr p) t p

(*
 * Subtyping.
 *)
interactive rfunction_rfunction_subtype {| intro_resource [] |} 'H 'a 'f lambda{a. lambda{b. 'R['a; 'b]}} :
   [main] sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   [wf] sequent [squash] { 'H >- "type"{.{f1 | x1: 'A1 -> 'B1['f1; 'x1] }} } -->
   [wf] sequent [squash] { 'H >- "type"{.{f2 | x2: 'A2 -> 'B2['f2; 'x2] }} } -->
   [wf] sequent [squash] { 'H; a1: 'A1; a2: 'A1 >- "type"{'R['a; 'b]} } -->
   [main] sequent [squash] { 'H; f: {f1 | x1: 'A1 -> 'B1['f1; 'x1]}; a: 'A2 >-
                          subtype{'B1['f; 'a]; 'B2['f; 'a]}
                    } -->
   sequent ['ext] { 'H >- subtype{.{ f1 | x1: 'A1 -> 'B1['f1; 'x1] }; .{ f2 | x2: 'A2 -> 'B2['f2; 'x2] } } }

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * We handle extensionality explicitly.
 *)
let rfunction_extensionalityT t1 t2 p =
   let t, _, _ = dest_equal (Sequent.concl p) in
   let _, v, _, _ = dest_rfun t in
   let v = maybe_new_vars1 p v in
      rfunctionExtensionality (Sequent.hyp_count_addr p) t1 t2 v p

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_rfun inf decl t =
   let f, v, a, b = dest_rfun t in
   let decl', a' = inf decl a in
   let decl'', b' = inf (add_unify_subst v a (add_unify_subst f (mk_fun_term a void_term) decl')) b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2 0)

let typeinf_resource = Mp_resource.improve typeinf_resource (rfun_term, inf_rfun)

(*
 * Type of lambda.
 *)
let inf_lambda (f : typeinf_func) (decl : unify_subst) (t : term) =
   let v, b = dest_lambda t in
   let a = new_unify_var decl v in
   let decl', b' = f (add_unify_subst v (mk_var_term a) decl) b in
   let decl'', a' =
(*
      try decl', List.assoc a decl' with
         Not_found ->
*)
            (add_unify_subst a void_term decl'), void_term
   in
      decl'', mk_dfun_term v a' b'

let typeinf_resource = Mp_resource.improve typeinf_resource (lambda_term, inf_lambda)

(*
 * Type of apply.
 *)
let inf_apply inf decl t =
   let f, a = dest_apply t in
   let decl', f' = inf decl f in
   let decl'', a' = inf decl' a in
   let ty =
      if is_dfun_term f' then
         let v, d, r = dest_dfun f' in
            subst r [a] [v]
      else if is_fun_term f' then
         let _, r = dest_fun f' in
            r
      else if is_rfun_term f' then
         let f'', v, d, r = dest_rfun f' in
            subst r [f; a] [f''; v]
      else
         raise  (RefineError ("typeinf", StringTermError ("can't infer type for", t)))
   in
      decl'', ty

let typeinf_resource = Mp_resource.improve typeinf_resource (apply_term, inf_apply)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
