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
include Itt_struct
include Itt_rfun

open Printf
open Mp_debug
open String_set
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Sequent
open Tacticals
open Conversionals
open Typeinf

open Base_dtactic

open Itt_equal
open Itt_struct
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_union%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare union{'A; 'B}
declare inl{'x}
declare inr{'x}
declare decide{'x; y. 'a['y]; z. 'b['z]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Reduction on decide.
 * decide(inl x; u. l[u]; v. r[v]) <--> l[x]
 * decide(inr x; u. l[u]; v. r[v]) <--> r[x]
 *)
prim_rw reduceDecideInl : decide{inl{'x}; u. 'l['u]; v. 'r['v]} <--> 'l['x]
prim_rw reduceDecideInr : decide{inr{'x}; u. 'l['u]; v. 'r['v]} <--> 'r['x]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_inl
prec prec_union

dform union_df : mode[prl] :: parens :: "prec"[prec_union] :: union{'A; 'B} =
   slot{'A} " " `"+" " " slot{'B}

dform inl_df : mode[prl] :: parens :: "prec"[prec_inl] :: inl{'a} =
   `"inl" " " slot{'a}

dform inr_df : mode[prl] :: parens :: "prec"[prec_inl] :: inr{'a} =
   `"inr" " " slot{'a}

dform decide_df : mode[prl] :: decide{'x; y. 'a; z. 'b} =
   szone pushm[0] pushm[3] `"match" " " slot{'x} " " `"with" hspace
   `"inl " slot{'y} `" -> " slot{'a} popm hspace
   pushm[3] `" | inr " slot{'z} `" -> " slot{'b} popm popm ezone

(************************************************************************
 * REDUCTIONS                                                           *
 ************************************************************************)

let reduce_info =
   [<< decide{inl{'x}; y. 'a['y]; z. 'b['z]} >>, reduceDecideInl;
    << decide{inr{'x}; y. 'a['y]; z. 'b['z]} >>, reduceDecideInr]

let reduce_resource = add_reduce_info reduce_resource reduce_info

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext A + B
 * by unionFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
prim unionFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[@i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   'A + 'B

(*
 * H >- A1 + B1 = A2 + B2 in Ui
 * by unionEquality
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
prim unionEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- 'A1 + 'B1 = 'A2 + 'B2 in univ[@i:l] } =
   it

(*
 * Typehood.
 *)
prim unionType 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{. 'A + 'B } } =
   it

(*
 * H >- A + B ext inl a
 * by inlFormation
 * H >- A
 * H >- B = B in Ui
 *)
prim inlFormation 'H :
   ('a : sequent ['ext] { 'H >- 'A }) -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- 'A + 'B } =
   inl{'a}

(*
 * H >- A + B ext inl a
 * by inrFormation
 * H >- B
 * H >- A = A in Ui
 *)
prim inrFormation 'H :
   ('b : sequent ['ext] { 'H >- 'B }) -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- 'A + 'B } =
   inr{'b}

(*
 * H >- inl a1 = inl a2 in A + B
 * by inlEquality
 * H >- a1 = a2 in A
 * H >- B = B in Ui
 *)
prim inlEquality 'H :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- inl{'a1} = inl{'a2} in 'A + 'B } =
   it

(*
 * H >- inr b1 = inr b2 in A + B
 * by inrEquality
 * H >- b1 = b2 in B
 * H >- A = A in Ui
 *)
prim inrEquality 'H :
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- inr{'b1} = inr{'b2} in 'A + 'B } =
   it

(*
 * H, x: A + B, J[x] >- T[x] ext decide(x; u. 'left['u]; v. 'right['v])
 * by unionElimination x u v
 * H, x: A # B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
prim unionElimination 'H 'J 'x 'u 'v :
   ('left['u] : sequent ['ext] { 'H; x: 'A + 'B; u: 'A; 'J[inl{'u}] >- 'T[inl{'u}] }) -->
   ('right['u] : sequent ['ext] { 'H; x: 'A + 'B; v: 'B; 'J[inr{'v}] >- 'T[inr{'v}] }) -->
   sequent ['ext] { 'H; x: 'A + 'B; 'J['x] >- 'T['x] } =
   decide{'x; u. 'left['u]; v. 'right['v]}

(*
 * H >- decide(e1; u1. l1[u1]; v1. r1[v1]) = decide(e2; u2. l2[u2]; v2. r2[v2]) in T[e1]
 * by unionEquality lambda(z. T[z]) (A + B) u v w
 * H >- e1 = e2 in A + B
 * H, u:A, w: e1 = inl u in A + B >- l1[u] = l2[u] in T[inl{u}]
 * H, v:A, w: e1 = inr v in A + B >- r1[v] = r2[v] in T[inr{v}]
 *)
prim decideEquality 'H lambda{z. 'T['z]} ('A + 'B) 'u 'v 'w :
   sequent [squash] { 'H >- 'e1 = 'e2 in 'A + 'B } -->
   sequent [squash] { 'H; u: 'A; w: 'e1 = inl{'u} in 'A + 'B >- 'l1['u] = 'l2['u] in 'T[inl{'u}] } -->
   sequent [squash] { 'H; v: 'B; w: 'e1 = inr{'v} in 'A + 'B >- 'r1['v] = 'r2['v] in 'T[inr{'v}] } -->
   sequent ['ext] { 'H >- decide{'e1; u1. 'l1['u1]; v1. 'r1['v1]} =
                   decide{'e2; u2. 'l2['u2]; v2. 'r2['v2]} in
                   'T['e1] } =
   it

(*
 * H >- A1 + B1 <= A2 + B2
 * by unionSubtype
 *
 * H >- A1 <= A2
 * H >- B1 <= B2
 *)
prim unionSubtype 'H :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 + 'B1); ('A2 + 'B2) } } =
   it

(*
 * Interactive.
 *)
interactive union_contradiction1 'H 'J : :
   sequent ['ext] { 'H; x: inl{'y} = inr{'z} in 'T; 'J['x] >- 'C['x] }

interactive union_contradiction2 'H 'J : :
   sequent ['ext] { 'H; x: inr{'y} = inl{'z} in 'T; 'J['x] >- 'C['x] }

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let union_term = << 'A + 'B >>
let union_opname = opname_of_term union_term
let is_union_term = is_dep0_dep0_term union_opname
let dest_union = dest_dep0_dep0_term union_opname
let mk_union_term = mk_dep0_dep0_term union_opname

let inl_term = << inl{'x} >>
let inl_opname = opname_of_term inl_term
let is_inl_term = is_dep0_term inl_opname
let dest_inl = dest_dep0_term inl_opname
let mk_inl_term = mk_dep0_term inl_opname

let inr_term = << inr{'x} >>
let inr_opname = opname_of_term inr_term
let is_inr_term = is_dep0_term inr_opname
let dest_inr = dest_dep0_term inr_opname
let mk_inr_term = mk_dep0_term inr_opname

let decide_term = << decide{'x; y. 'a['y]; z. 'b['z]} >>
let decide_opname = opname_of_term decide_term
let is_decide_term = is_dep0_dep1_dep1_term decide_opname
let dest_decide = dest_dep0_dep1_dep1_term decide_opname
let mk_decide_term = mk_dep0_dep1_dep1_term decide_opname

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_union p =
   let count = hyp_count_addr p in
   let flag =
      try get_sel_arg p with
         Not_found ->
            raise (RefineError ("d_concl_union", StringError "requires a flag"))
   in
   let tac =
      match flag with
         1 ->
            inlFormation
       | 2 ->
            inrFormation
       | _ ->
            raise (RefineError ("d_concl_union", StringError "select either 1 or 2"))
   in
      (tac count thenLT [idT; addHiddenLabelT "wf"]) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_union i p =
   let count = hyp_count_addr p in
   let z, _ = Sequent.nth_hyp p i in
   let j, k = hyp_indices p i in
   let u, v = maybe_new_vars2 p z z in
      (unionElimination j k z u v thenT thinT i) p

(*
 * Join them.
 *)
let d_unionT i =
   if i = 0 then
      d_concl_union
   else
      d_hyp_union i

let d_resource = Mp_resource.improve d_resource (union_term, d_unionT)

(*
 * Typehood.
 *)
let d_union_typeT i p =
   if i = 0 then
      unionType (hyp_count_addr p) p
   else
      raise (RefineError ("d_union_typeT", StringError "no elimination form"))

let union_type_term = << "type"{. 'A + 'B } >>

let d_resource = Mp_resource.improve d_resource (union_type_term, d_union_typeT)

(*
 * Contradiction.
 *)
let d_contradiction1 i p =
   let j, k = Sequent.hyp_indices p i in
      union_contradiction1 j k p

let d_contradiction2 i p =
   let j, k = Sequent.hyp_indices p i in
      union_contradiction2 j k p

let d_info =
   [<< inl{'x} = inr{'y} in 'T >>, wrap_elim d_contradiction1;
    << inr{'x} = inl{'y} in 'T >>, wrap_elim d_contradiction2]

let d_resource = add_d_info d_resource d_info

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

(*
 * EQCD union.
 *)
let eqcd_unionT p =
   let count = hyp_count_addr p in
      (unionEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = Mp_resource.improve eqcd_resource (union_term, eqcd_unionT)

let union_equal_term = << ('a1 + 'a2) = ('b1 + 'b2) in univ[@i:l] >>

let d_resource = Mp_resource.improve d_resource (union_equal_term, d_wrap_eqcd eqcd_unionT)

(*
 * EQCD inl.
 *)
let eqcd_inlT p =
   let count = hyp_count_addr p in
      (inlEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = Mp_resource.improve eqcd_resource (inl_term, eqcd_inlT)

let inl_equal_term = << inl{'x1} = inl{'x2} in ('a1 + 'a2) >>

let d_resource = Mp_resource.improve d_resource (inl_equal_term, d_wrap_eqcd eqcd_inlT)

(*
 * EQCD inr.
 *)
let eqcd_inrT p =
   let count = hyp_count_addr p in
      (inrEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = Mp_resource.improve eqcd_resource (inr_term, eqcd_inrT)

let inr_equal_term = << inr{'x1} = inr{'x2} in ('a1 + 'a2) >>

let d_resource = Mp_resource.improve d_resource (inr_equal_term, d_wrap_eqcd eqcd_inrT)

(*
 * EQCD decide.
 *)
let eqcd_decideT p =
   raise (RefineError ("eqcd_decideT", StringError "not implemented"))

let eqcd_resource = Mp_resource.improve eqcd_resource (decide_term, eqcd_decideT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of disjoint union.
 *)
let inf_union f decl t =
   let a, b = dest_union t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2 0)

let typeinf_resource = Mp_resource.improve typeinf_resource (union_term, inf_union)

(*
 * Type of inl.
 *)
let inf_inl f decl t =
   let a = dest_inl t in
   let decl', a' = f decl a in
      decl', mk_union_term a' (mk_var_term (new_unify_var decl' "T"))

let typeinf_resource = Mp_resource.improve typeinf_resource (inl_term, inf_inl)

(*
 * Type of inr.
 *)
let inf_inr f decl t =
   let a = dest_inr t in
   let decl', a' = f decl a in
      decl', mk_union_term (mk_var_term (new_unify_var decl' "T")) a'

let typeinf_resource = Mp_resource.improve typeinf_resource (inr_term, inf_inr)

(*
 * Type of decide.
 *)
let inf_decide (inf : typeinf_func) (decl : unify_subst) (t : term) =
   let e, x, a, y, b = dest_decide t in
   let decl', e' = inf decl e in
   let l, r = dest_union e' in
   let decl'', a' = inf (add_unify_subst x l decl') a in
   let decl''', b' = inf (add_unify_subst y l decl'') b in
      unify decl''' StringSet.empty a' b', a'

let typeinf_resource = Mp_resource.improve typeinf_resource (decide_term, inf_decide)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two union types.
 *)
let union_subtypeT p =
   (unionSubtype (hyp_count_addr p)
    thenT addHiddenLabelT "subtype") p

let sub_resource =
   Mp_resource.improve
   sub_resource
   (DSubtype ([<< 'A1 + 'B1 >>, << 'A2 + 'B2 >>;
               << 'A1 >>, << 'A2 >>;
               << 'B1 >>, << 'B2 >>],
              union_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
