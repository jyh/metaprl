(*
 * Rules for dependent product.
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
include Itt_struct
include Itt_subtype

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
open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Typeinf
open Base_dtactic

open Itt_equal
open Itt_subtype
open Itt_struct
open Itt_rfun

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_dprod%t" eflush

(* debug_string DebugLoad "Loading itt_dprod..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(* declare prod{'A; 'B} *)
declare prod{'A; x. 'B['x]}
declare pair{'a; 'b}
declare spread{'e; u, v. 'b['u; 'v]}
declare fst{'e}
declare snd{'e}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Reduction on spread:
 * spread(u, v; a, b. c[a, b]) <--> c[u, v]
 *)
prim_rw reduceSpread : spread{'u, 'v; a, b. 'c['a; 'b]} <--> 'c['u; 'v]

prim_rw unfoldFst : fst{'e} <--> spread{'e; u, v. 'u}
prim_rw unfoldSnd : fst{'e} <--> spread{'e; u, v. 'v}

prim_rw reduceFst : fst{pair{'a; 'b}} <--> 'a
prim_rw reduceSnd : snd{pair{'a; 'b}} <--> 'b

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_prod
prec prec_spread

dform prod_src_df : parens :: "prec"[prec_prod] :: mode[src] :: prod{'A; 'B} =
   slot{'A} `" * " slot{'B}

dform prod_prl_df : parens :: "prec"[prec_prod] :: prod{'A; 'B} =
   pushm[0] slot{'A} " " times " " slot{'B} popm

dform prod_src_df2 : parens :: "prec"[prec_prod] :: mode[src] :: prod{'A; x. 'B} =
   slot{'x} `":" slot{'A} `" * " slot{'B}

dform prod_prl_df2 :  parens :: "prec"[prec_prod] :: prod{'A; x. 'B} =
   slot{'x} `":" slot{'A} " " times " " slot{'B}

dform pair_prl_df1 : pair{'a; 'b} =
   pushm[0] `"<" slot{'a}`"," slot{'b} `">" popm

dform spread_prl_df1 : parens :: "prec"[prec_spread] :: spread{'e; u, v. 'b} =
   `"let " pair{'u; 'v} `" = " slot{'e} `" in " slot{'b}

dform fst_df1 : fst{'e} =
   slot{'e} `".1"

dform snd_df1 : snd{'e} =
   slot{'e} `".2"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext x:A * B
 * by productFormation A x
 * H >- A = A in Ui
 * H, x:A >- Ui ext B
 *)
prim productFormation 'H 'A 'x :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'A} } -->
   [main] ('B['x] : sequent ['ext] { 'H; x: 'A >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   x:'A * 'B['x]

(*
 * H >- x1:A1 * B1 = x2:A2 * B2 in Ui
 * by productEquality y
 * H >- A1 = A2 in Ui
 * H, y:A1 >- B1[y] = B2[y] in Ui
 *)
prim productEquality {| intro_resource []; eqcd_resource |} 'H 'y :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent ['ext] { 'H >- x1:'A1 * 'B1['x1] = x2:'A2 * 'B2['x2] in univ[i:l] } =
   it

interactive productMember {| intro_resource [] |} 'H 'y :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'A1} } -->
   [wf] sequent [squash] { 'H; y: 'A1 >- member{univ[i:l]; 'B1['y]} } -->
   sequent ['ext] { 'H >- member{.univ[i:l]; .x1:'A1 * 'B1['x1]} }

(*
 * Typehood.
 *)
prim productType {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A1} } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- "type"{'A2['x]} } -->
   sequent ['ext] { 'H >- "type"{.y:'A1 * 'A2['y]} } =
   it

(*
 * H >- x:A * B ext (a, b)
 * by pairFormation a y
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
prim pairFormation {| intro_resource [] |} 'H 'a 'y :
   [wf] sequent [squash] { 'H >- member{'A; 'a} } -->
   [main] ('b : sequent ['ext] { 'H >- 'B['a] }) -->
   [wf] sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- x:'A * 'B['x] } =
   'a, 'b

(*
 * H >- (a1, b1) = (a2, b2) in x:A * B
 * by pairEquality y
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B[a1]
 * H, y:A >- B[y] = B[y] in Ui
 *)
prim pairEquality {| intro_resource []; eqcd_resource |} 'H 'y :
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   [wf] sequent [squash] { 'H >- 'b1 = 'b2 in 'B['a1] } -->
   [wf] sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- ('a1, 'b1) = ('a2, 'b2) in x:'A * 'B['x] } =
   it

interactive pairMember {| intro_resource [] |} 'H 'y :
   [wf] sequent [squash] { 'H >- member{'A; 'a1} } -->
   [wf] sequent [squash] { 'H >- member{'B['a1]; 'b1} } -->
   [wf] sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- member{.x:'A * 'B['x]; .('a1, 'b1)} }

(*
 * H, x:A * B[x], J[x] >- T[x] ext spread(x; u, v. t[u, v])
 * by productElimination u v
 * H, x:A * B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
prim productElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'z 'u 'v :
   [wf] ('t['u; 'v] : sequent ['ext] { 'H; z: x:'A * 'B['x]; u: 'A; v: 'B['u]; 'J['u, 'v] >- 'T['u, 'v] }) -->
   sequent ['ext] { 'H; z: x:'A * 'B['x]; 'J['z] >- 'T['z] } =
   spread{'z; u, v. 't['u; 'v]}

(*
 * H >- spread(e1; u1, v1. b1) = spread(e2; u2, v2. b2) in T[e1]
 * by spreadEquality (w:A * B)
 * H >- e1 = e2 in w:A * B
 * H, u:A, v: B[u], a: e1 = (u, v) in w:A * B >- b1[u; v] = b2[u; v] in T[u, v]
 *)
prim spreadEquality {| intro_resource []; eqcd_resource |} 'H bind{z. 'T['z]} (w:'A * 'B['w]) 'u 'v 'a :
   [wf] sequent [squash] { 'H >- 'e1 = 'e2 in w:'A * 'B['w] } -->
   [wf] sequent [squash] { 'H; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >-
             'b1['u; 'v] = 'b2['u; 'v] in 'T['u, 'v] } -->
   sequent ['ext] { 'H >- spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T['e1] } =
   it

interactive spreadMember {| intro_resource [] |} 'H bind{z. 'T['z]} (w:'A * 'B['w]) 'u 'v 'a :
   [wf] sequent [squash] { 'H >- member{.w:'A * 'B['w]; 'e1} } -->
   [wf] sequent [squash] { 'H; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >- member{'T['u, 'v]; 'b1['u; 'v]} } -->
   sequent ['ext] { 'H >- member{'T['e1]; spread{'e1; u1, v1. 'b1['u1; 'v1]}} }

(*
 * H >- a1:A1 * B1 <= a2:A2 * B2
 * by functionSubtype
 *
 * H >- A1 <= A2
 * H, a: A1 >- B1[a] <= B2[a]
 *)
prim productSubtype {| intro_resource [] |} 'H 'a :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { 'H >- subtype{ (a1:'A1 * 'B1['a1]); (a2:'A2 * 'B2['a2]) } } =
   it

(************************************************************************
 * REDUCTION                                                            *
 ************************************************************************)

let reduce_info =
   [<< spread{pair{'u; 'v}; x, y. 'b['x; 'y]} >>, reduceSpread;
    << fst{pair{'u; 'v}} >>, reduceFst;
    << snd{pair{'u; 'v}} >>, reduceSnd]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let dprod_term = << x: 'A * 'B['x] >>
let dprod_opname = opname_of_term dprod_term
let is_dprod_term = is_dep0_dep1_term dprod_opname
let dest_dprod = dest_dep0_dep1_term dprod_opname
let mk_dprod_term = mk_dep0_dep1_term dprod_opname

let prod_term = << 'A * 'B >>
let prod_opname = opname_of_term prod_term
let is_prod_term = is_dep0_dep0_term prod_opname
let dest_prod = dest_dep0_dep0_term prod_opname
let mk_prod_term = mk_dep0_dep0_term prod_opname

let pair_term = << pair{'a; 'b} >>
let pair_opname = opname_of_term pair_term
let is_pair_term = is_dep0_dep0_term pair_opname
let dest_pair = dest_dep0_dep0_term pair_opname
let mk_pair_term = mk_dep0_dep0_term pair_opname

let spread_term = << spread{'e; u, v. 'b['u; 'v]} >>
let spread_opname = opname_of_term spread_term
let is_spread_term = is_dep0_dep2_term spread_opname
let dest_spread = dest_dep0_dep2_term spread_opname
let mk_spread_term = mk_dep0_dep2_term spread_opname

(************************************************************************
 * SPREAD EQUALITY                                                      *
 ************************************************************************)

(*
 * These require type inference.
 *)
let d_spread_equalT p =
   let rt, spread =
      try
         let rt, spread, _ = dest_equal (Sequent.concl p) in
            rt, spread
      with
         RefineError _ ->
            dest_member (Sequent.concl p)
   in
   let v = maybe_new_vars1 p "v" in
   let type_type = mk_bind_term v rt in
   let _, _, pair, _ = dest_spread spread in
   let type_type, pair_type =
      try
         match get_with_args p with
            type_type :: pair_type :: _ ->
               type_type, pair_type
          | [pair_type] ->
               type_type, pair_type
          | [] ->
               raise (RefineError ("d_spread_equalT", StringError "terms are required"))
      with
         RefineError _ ->
            type_type, snd (infer_type p pair)
   in
      (withTermsT [type_type; pair_type] (dT 0)) p

let spread_equal_term = << spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T >>

let intro_resource = Mp_resource.improve intro_resource (spread_equal_term, d_spread_equalT)

let spread_member_term = << member{'T; spread{'e1; u1, v1. 'b1['u1; 'v1]}} >>

let intro_resource = Mp_resource.improve intro_resource (spread_member_term, d_spread_equalT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_dprod f decl t =
   let v, a, b = dest_dprod t in
   let decl', a' = f decl a in
   let decl'', b' = f (add_unify_subst v a decl') b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2 0)

let typeinf_resource = Mp_resource.improve typeinf_resource (dprod_term, inf_dprod)

(*
 * Type of pair.
 *)
let inf_pair f decl t =
   let a, b = dest_pair t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
      decl'', mk_prod_term a' b'

let typeinf_resource = Mp_resource.improve typeinf_resource (pair_term, inf_pair)

(*
 * Type of spread.
 *)
let inf_spread inf decl t =
   let u, v, a, b = dest_spread t in
   let decl', a' = inf decl a in
      if is_prod_term a' then
         let l, r = dest_prod a' in
            inf (add_unify_subst u l (add_unify_subst v r decl')) b
      else if is_dprod_term a' then
         let x, l, r = dest_dprod a' in
            inf (add_unify_subst u l (add_unify_subst v (subst r [mk_var_term u] [x]) decl')) b
      else
         raise (RefineError ("typeinf", StringTermError ("can't infer type for", t)))

let typeinf_resource = Mp_resource.improve typeinf_resource (spread_term, inf_spread)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let dprod_subtypeT p =
   let a = get_opt_var_arg "x" p in
      (productSubtype (Sequent.hyp_count_addr p) a
       thenT addHiddenLabelT "subtype") p

let sub_resource =
   Mp_resource.improve
   sub_resource
   (DSubtype ([<< a1:'A1 * 'B1['a1] >>, << a2:'A2 * 'B2['a2] >>;
               << 'A1 >>, << 'A2 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              dprod_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
