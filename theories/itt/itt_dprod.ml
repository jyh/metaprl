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

include Tacticals

include Itt_equal
include Itt_rfun
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
open Tacticals
open Conversionals
open Sequent

open Itt_equal
open Itt_subtype
open Itt_struct

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

dform prod_prl_df : parens :: "prec"[prec_prod] :: mode[prl] :: prod{'A; 'B} =
   pushm[0] slot{'A} " " times " " slot{'B} popm

dform prod_src_df2 : parens :: "prec"[prec_prod] :: mode[src] :: prod{'A; x. 'B} =
   slot{'x} `":" slot{'A} `" * " slot{'B}

dform prod_prl_df2 :  parens :: "prec"[prec_prod] :: mode[prl] :: prod{'A; x. 'B} =
   slot{'x} `":" slot{'A} " " times " " slot{'B}

dform pair_prl_df1 : mode[prl] :: pair{'a; 'b} =
   pushm[0] `"<" slot{'a}`"," slot{'b} `">" popm

dform spread_prl_df1 : parens :: "prec"[prec_spread] :: mode[prl] :: spread{'e; u, v. 'b} =
   `"let " pair{'u; 'v} `" = " slot{'e} `" in " slot{'b}

dform fst_df1 : mode[prl] :: fst{'e} =
   slot{'e} `".1"

dform snd_df1 : mode[prl] :: snd{'e} =
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
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   ('B['x] : sequent ['ext] { 'H; x: 'A >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   x:'A * 'B['x]

(*
 * H >- x1:A1 * B1 = x2:A2 * B2 in Ui
 * by productEquality y
 * H >- A1 = A2 in Ui
 * H, y:A1 >- B1[y] = B2[y] in Ui
 *)
prim productEquality 'H 'y :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[@i:l] } -->
   sequent ['ext] { 'H >- x1:'A1 * 'B1['x1] = x2:'A2 * 'B2['x2] in univ[@i:l] } =
   it

(*
 * Typehood.
 *)
prim productType 'H 'x :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H; x: 'A1 >- "type"{'A2['x]} } -->
   sequent ['ext] { 'H >- "type"{.y:'A1 * 'A2['y]} } =
   it

(*
 * H >- x:A * B ext (a, b)
 * by pairFormation a y
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
prim pairFormation 'H 'a 'y :
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   ('b : sequent ['ext] { 'H >- 'B['a] }) -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- x:'A * 'B['x] } =
   'a, 'b

(*
 * H >- (a1, b1) = (a2, b2) in x:A * B
 * by pairEquality y
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B[a1]
 * H, y:A >- B[y] = B[y] in Ui
 *)
prim pairEquality 'H 'y :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B['a1] } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- ('a1, 'b1) = ('a2, 'b2) in x:'A * 'B['x] } =
   it

(*
 * H, x:A * B[x], J[x] >- T[x] ext spread(x; u, v. t[u, v])
 * by productElimination u v
 * H, x:A * B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
prim productElimination 'H 'J 'z 'u 'v :
   ('t['u; 'v] : sequent ['ext] { 'H; z: x:'A * 'B['x]; u: 'A; v: 'B['u]; 'J['u, 'v] >- 'T['u, 'v] }) -->
   sequent ['ext] { 'H; z: x:'A * 'B['x]; 'J['z] >- 'T['z] } =
   spread{'z; u, v. 't['u; 'v]}

(*
 * H >- spread(e1; u1, v1. b1) = spread(e2; u2, v2. b2) in T[e1]
 * by spreadEquality (w:A * B)
 * H >- e1 = e2 in w:A * B
 * H, u:A, v: B[u], a: e1 = (u, v) in w:A * B >- b1[u; v] = b2[u; v] in T[u, v]
 *)
prim spreadEquality 'H lambda{z. 'T['z]} (w:'A * 'B['w]) 'u 'v 'a :
   sequent [squash] { 'H >- 'e1 = 'e2 in w:'A * 'B['w] } -->
   sequent [squash] { 'H; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >-
             'b1['u; 'v] = 'b2['u; 'v] in 'T['u, 'v] } -->
   sequent ['ext] { 'H >- spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T['e1] } =
   it

(*
 * H >- a1:A1 * B1 <= a2:A2 * B2
 * by functionSubtype
 *
 * H >- A1 <= A2
 * H, a: A1 >- B1[a] <= B2[a]
 *)
prim productSubtype 'H 'a :
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

let reduce_resource = add_reduce_info reduce_resource reduce_info

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
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_dprod p =
   let t =
      try get_with_arg p with
         Not_found -> raise (RefineError ("d_concl_dprod", StringError "requires an argument"))
   in
   let count = hyp_count_addr p in
   let y = get_opt_var_arg "y" p in
      (pairFormation count t y
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "main";
               addHiddenLabelT "wf"]) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_dprod i p =
   let z, _ = Sequent.nth_hyp p i in
   let i', j = hyp_indices p i in
   let u, v = maybe_new_vars2 p "u" "v" in
   let tac = productElimination i' j z u v in
      if get_thinning_arg p then
         (tac thenT thinT i) p
      else
         tac p

(*
 * Join them.
 *)
let d_dprodT i =
   if i = 0 then
      d_concl_dprod
   else
      d_hyp_dprod i

let d_resource = Mp_resource.improve d_resource (dprod_term, d_dprodT)

(*
 * Typehood.
 *)
let d_dprod_typeT i p =
   if i = 0 then
      let concl = Sequent.concl p in
      let v, _, _ = dest_dprod (one_subterm concl) in
      let v = maybe_new_vars1 p v in
         productType (hyp_count_addr p) v p
   else
      raise (RefineError ("d_prod_typeT", StringError "no elimination form"))

let type_dprod_term = << "type"{.x:'A1 * 'A2['x]} >>

let d_resource = Mp_resource.improve d_resource (type_dprod_term, d_dprod_typeT)

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

(*
 * EQCD dprod.
 *)
let eqcd_dprodT p =
   let _, l, _ = dest_equal (concl p) in
   let v, _, _ = dest_dprod l in
   let x = get_opt_var_arg v p in
   let count = hyp_count_addr p in
      (productEquality count x
       thenT addHiddenLabelT "wf") p

let eqcd_resource = Mp_resource.improve eqcd_resource (dprod_term, eqcd_dprodT)

let dprod_equal_term = << (x1 : 'A1 * 'B1['x1]) = (x2 : 'A2 * 'B2['x2]) in univ[@i:l] >>

let d_resource = Mp_resource.improve d_resource (dprod_equal_term, d_wrap_eqcd eqcd_dprodT)

(*
 * EQCD pair.
 *)
let eqcd_pairT p =
   let l, _, _ = dest_equal (concl p) in
   let v, _, _ = dest_dprod l in
   let x = get_opt_var_arg v p in
   let count = hyp_count_addr p in
      (pairEquality count x
       thenT addHiddenLabelT "wf") p

let eqcd_resource = Mp_resource.improve eqcd_resource (pair_term, eqcd_pairT)

let dpair_equal_term = << ('a1, 'b1) = ('a2, 'b2) in (x1 : 'A1 * 'B1['x1]) >>

let d_resource = Mp_resource.improve d_resource (dpair_equal_term, d_wrap_eqcd eqcd_pairT)

(*
 * EQCD spread.
 *)
let eqcd_spreadT p =
   let _, l, _ = dest_equal (concl p) in
   let u, v, _, _ = dest_spread l in
      raise (RefineError ("eqcd_spreadT", StringError "not implemented"))

let eqcd_resource = Mp_resource.improve eqcd_resource (spread_term, eqcd_spreadT)

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
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

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
      (productSubtype (hyp_count_addr p) a
       thenT addHiddenLabelT "subtype") p

let sub_resource =
   Mp_resource.improve
   sub_resource
   (DSubtype ([<< a1:'A1 * 'B1['a1] >>, << a2:'A2 * 'B2['a2] >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              dprod_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
