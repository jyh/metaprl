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

include Itt_void
include Itt_equal
include Itt_struct
include Itt_subtype

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
open Tactic_type.Sequent
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_dtactic

open Itt_equal
open Itt_struct
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_union%t"

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

dform union_df : parens :: "prec"[prec_union] :: union{'A; 'B} =
   slot{'A} " " `"+" " " slot{'B}

dform inl_df : parens :: "prec"[prec_inl] :: inl{'a} =
   `"inl" " " slot{'a}

dform inr_df : parens :: "prec"[prec_inl] :: inr{'a} =
   `"inr" " " slot{'a}

dform decide_df : decide{'x; y. 'a; z. 'b} =
   szone pushm[0] pushm[3] `"match" " " slot{'x} " " `"with" hspace
   `"inl " slot{'y} `" -> " slot{'a} popm hspace
   pushm[3] `" | inr " slot{'z} `" -> " slot{'b} popm popm ezone

(************************************************************************
 * REDUCTIONS                                                           *
 ************************************************************************)

let reduce_info =
   [<< decide{inl{'x}; y. 'a['y]; z. 'b['z]} >>, reduceDecideInl;
    << decide{inr{'x}; y. 'a['y]; z. 'b['z]} >>, reduceDecideInr]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

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
   ('A : sequent ['ext] { 'H >- univ[i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   'A + 'B

(*
 * H >- A1 + B1 = A2 + B2 in Ui
 * by unionEquality
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
prim unionEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- 'A1 + 'B1 = 'A2 + 'B2 in univ[i:l] } =
   it

interactive unionMember {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'A1} } -->
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'B1} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; .'A1 + 'B1} }

(*
 * Typehood.
 *)
prim unionType {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{. 'A + 'B } } =
   it

(*
 * H >- A + B ext inl a
 * by inlFormation
 * H >- A
 * H >- B = B in Ui
 *)
prim inlFormation {| intro_resource [SelectOption 1] |} 'H :
   [main] ('a : sequent ['ext] { 'H >- 'A }) -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- 'A + 'B } =
   inl{'a}

(*
 * H >- A + B ext inl a
 * by inrFormation
 * H >- B
 * H >- A = A in Ui
 *)
prim inrFormation {| intro_resource [SelectOption 2] |} 'H :
   [main] ('b : sequent ['ext] { 'H >- 'B }) -->
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- 'A + 'B } =
   inr{'b}

(*
 * H >- inl a1 = inl a2 in A + B
 * by inlEquality
 * H >- a1 = a2 in A
 * H >- B = B in Ui
 *)
prim inlEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- inl{'a1} = inl{'a2} in 'A + 'B } =
   it

interactive inlMember {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{'A; 'a1} } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- member{.'A + 'B; inl{'a1}} }

(*
 * H >- inr b1 = inr b2 in A + B
 * by inrEquality
 * H >- b1 = b2 in B
 * H >- A = A in Ui
 *)
prim inrEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'b1 = 'b2 in 'B } -->
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- inr{'b1} = inr{'b2} in 'A + 'B } =
   it

interactive inrMember {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{'B; 'b1} } -->
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- member{.'A + 'B; inr{'b1}} }

(*
 * H, x: A + B, J[x] >- T[x] ext decide(x; u. 'left['u]; v. 'right['v])
 * by unionElimination x u v
 * H, x: A # B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
prim unionElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'x 'u 'v :
   [left] ('left['u] : sequent ['ext] { 'H; x: 'A + 'B; u: 'A; 'J[inl{'u}] >- 'T[inl{'u}] }) -->
   [right] ('right['u] : sequent ['ext] { 'H; x: 'A + 'B; v: 'B; 'J[inr{'v}] >- 'T[inr{'v}] }) -->
   sequent ['ext] { 'H; x: 'A + 'B; 'J['x] >- 'T['x] } =
   decide{'x; u. 'left['u]; v. 'right['v]}

(*
 * H >- decide(e1; u1. l1[u1]; v1. r1[v1]) = decide(e2; u2. l2[u2]; v2. r2[v2]) in T[e1]
 * by unionEquality lambda(z. T[z]) (A + B) u v w
 * H >- e1 = e2 in A + B
 * H, u:A, w: e1 = inl u in A + B >- l1[u] = l2[u] in T[inl{u}]
 * H, v:A, w: e1 = inr v in A + B >- r1[v] = r2[v] in T[inr{v}]
 *)
prim decideEquality {| intro_resource []; eqcd_resource |} 'H bind{z. 'T['z]} ('A + 'B) 'u 'v 'w :
   [wf] sequent [squash] { 'H >- 'e1 = 'e2 in 'A + 'B } -->
   [wf] sequent [squash] { 'H; u: 'A; w: 'e1 = inl{'u} in 'A + 'B >- 'l1['u] = 'l2['u] in 'T[inl{'u}] } -->
   [wf] sequent [squash] { 'H; v: 'B; w: 'e1 = inr{'v} in 'A + 'B >- 'r1['v] = 'r2['v] in 'T[inr{'v}] } -->
   sequent ['ext] { 'H >- decide{'e1; u1. 'l1['u1]; v1. 'r1['v1]} =
                   decide{'e2; u2. 'l2['u2]; v2. 'r2['v2]} in
                   'T['e1] } =
   it

interactive decideMember {| intro_resource []; eqcd_resource |} 'H bind{z. 'T['z]} ('A + 'B) 'u 'v 'w :
   [wf] sequent [squash] { 'H >- member{.'A + 'B; 'e1} } -->
   [wf] sequent [squash] { 'H; u: 'A; w: 'e1 = inl{'u} in 'A + 'B >- member{'T[inl{'u}]; 'l1['u]} } -->
   [wf] sequent [squash] { 'H; v: 'B; w: 'e1 = inr{'v} in 'A + 'B >- member{'T[inr{'v}]; 'r1['v]} } -->
   sequent ['ext] { 'H >- decide{'e1; u1. 'l1['u1]; v1. 'r1['v1]} =
                   decide{'e2; u2. 'l2['u2]; v2. 'r2['v2]} in
                   'T['e1] }

(*
 * H >- A1 + B1 <= A2 + B2
 * by unionSubtype
 *
 * H >- A1 <= A2
 * H >- B1 <= B2
 *)
prim unionSubtype {| intro_resource [] |} 'H :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 + 'B1); ('A2 + 'B2) } } =
   it

(*
 * Interactive.
 *)
interactive union_contradiction1 {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; x: inl{'y} = inr{'z} in 'T; 'J['x] >- 'C['x] }

interactive union_contradiction2 {| elim_resource [] |} 'H 'J :
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
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let typeinf_resource =
   Mp_resource.improve typeinf_resource (union_term, infer_univ_dep0_dep0 dest_union)

(*
 * Type of inl.
 *)
let inf_inl inf consts decls eqs opt_eqs defs t =
   let a = dest_inl t in
   let eqs', opt_eqs', defs', a' = inf consts decls eqs opt_eqs defs a in
   let b = Typeinf.vnewname consts defs' "T-r" in
       eqs', opt_eqs', ((b,<<void>>)::defs') , mk_union_term a' (mk_var_term b)

let typeinf_resource = Mp_resource.improve typeinf_resource (inl_term, inf_inl)

(*
 * Type of inr.
 *)
let inf_inr inf consts decls eqs opt_eqs defs t =
   let a = dest_inl t in
   let eqs', opt_eqs', defs', a' = inf consts decls eqs opt_eqs defs a in
   let b = Typeinf.vnewname consts defs' "T-l" in
       eqs', opt_eqs', ((b,<<void>>)::defs') , mk_union_term (mk_var_term b) a'

let typeinf_resource = Mp_resource.improve typeinf_resource (inr_term, inf_inr)

(*
 * Type of decide.
 *)
let inf_decide inf consts decls eqs opt_eqs defs t =
   let e, x, a, y, b = dest_decide t in
   let eqs', opt_eqs', defs', e' = inf consts decls eqs opt_eqs defs e in
   let consts = StringSet.add x (StringSet.add y consts) in
   let l = Typeinf.vnewname consts defs' "T-l" in
   let l' = mk_var_term l in
   let r = Typeinf.vnewname consts defs' "T-r" in
   let r' = mk_var_term r in
   let eqs'', opt_eqs'', defs'', a' =
      inf consts ((x, l')::decls)
          (eqnlist_append_eqn eqs' e' (mk_union_term l' r')) opt_eqs'
          ((l,<<top>>)::(r,<<top>>)::defs') a
   in
   let eqs''', opt_eqs''', defs''', b' =
      inf consts ((y, r')::decls) eqs'' opt_eqs'' defs'' b
   in eqs''', ((a',b')::opt_eqs'''), defs''', a'

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
