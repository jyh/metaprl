(*
 * Boolean operations.
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
 *)

include Itt_equal
include Itt_struct
include Itt_union
include Itt_set
include Itt_logic

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Var

open Base_dtactic
open Base_auto_tactic

open Itt_equal
open Itt_logic
open Itt_struct

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "bool"
declare "btrue"
declare "bfalse"
declare bor{'a; 'b}
declare band{'a; 'b}
declare bimplies{'a; 'b}
declare bnot{'a; 'b}

declare "assert"{'t}

declare ifthenelse{'e1; 'e2; 'e3}

(*
 * Definition of bool.
 *)
prim_rw unfold_bool : bool <--> (unit + unit)
prim_rw unfold_btrue : btrue <--> inl{it}
prim_rw unfold_bfalse : bfalse <--> inr{it}

(*
 * Ifthenelse primrws.
 *)
prim_rw unfold_ifthenelse : ifthenelse{'b; 'e1; 'e2} <--> decide{'b; x. 'e1; y. 'e2}
prim_rw unfold_bor : bor{'a; 'b} <--> ifthenelse{'a; btrue; 'b}
prim_rw unfold_band : band{'a; 'b} <--> ifthenelse{'a; 'b; bfalse}
prim_rw unfold_bimplies : bimplies{'a; 'b} <--> ifthenelse{'a; 'b; btrue}
prim_rw unfold_bnot : bnot{'a} <--> ifthenelse{'a; bfalse; btrue}
prim_rw unfold_assert : "assert"{'t} <--> ('t = btrue in bool)

let fold_bool = makeFoldC << bool >> unfold_bool
let fold_btrue = makeFoldC << btrue >> unfold_btrue
let fold_bfalse = makeFoldC << bfalse >> unfold_bfalse
let fold_bor = makeFoldC << bor{'a; 'b} >> unfold_bor
let fold_band = makeFoldC << band{'a; 'b} >> unfold_band
let fold_bimplies = makeFoldC << bimplies{'a; 'b} >> unfold_bimplies
let fold_bnot = makeFoldC << bnot{'a} >> unfold_bnot
let fold_assert = makeFoldC << "assert"{'t} >> unfold_assert

interactive_rw reduce_ifthenelse_true : ifthenelse{btrue; 'e1; 'e2} <--> 'e1
interactive_rw reduce_ifthenelse_false : ifthenelse{bfalse; 'e1; 'e2} <--> 'e2

let reduce_info =
   [<< ifthenelse{btrue; 'e1; 'e2} >>, reduce_ifthenelse_true;
    << ifthenelse{bfalse; 'e1; 'e2} >>, reduce_ifthenelse_false]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

(************************************************************************
 * REDUCTIONS                                                           *
 ************************************************************************)

interactive_rw reduce_bnot_true : bnot{btrue} <--> bfalse

interactive_rw reduce_bnot_false : bnot{bfalse} <--> btrue

interactive_rw reduce_bor_true : bor{btrue; 'e1} <--> btrue

interactive_rw reduce_bor_false : bor{bfalse; 'e1} <--> 'e1

interactive_rw reduce_band_true : band{btrue; 'e1} <--> 'e1

interactive_rw reduce_band_false : band{bfalse; 'e1} <--> bfalse

interactive_rw reduce_bimplies_true : bimplies{btrue; 'e1} <--> 'e1

interactive_rw reduce_bimplies_false : bimplies{bfalse; 'e1} <--> btrue

let reduce_info =
   [<< bnot{btrue} >>, reduce_bnot_true;
    << bnot{bfalse} >>, reduce_bnot_false;
    << bor{btrue; 'e1} >>, reduce_bor_true;
    << bor{bfalse; 'e1} >>, reduce_bor_false;
    << band{btrue; 'e1} >>, reduce_band_true;
    << band{bfalse; 'e1} >>, reduce_band_false;
    << bimplies{btrue; 'e1} >>, reduce_bimplies_true;
    << bimplies{bfalse; 'e1} >>, reduce_bimplies_false]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

(*
 * Precedences:
 *
 * implies < or < and < not < assert
 *)
prec prec_bimplies
prec prec_bor
prec prec_band
prec prec_bnot
prec prec_assert

prec prec_bimplies < prec_bor
prec prec_bor < prec_band
prec prec_band < prec_bnot
prec prec_bnot < prec_assert

dform bool_df : bool =
   `"Bool"

dform btrue_df : btrue =
   `"true"

dform bfalse_df : bfalse =
   `"false"

dform bor_df : parens :: "prec"[prec_bor] :: bor{'a; 'b} =
   slot{'a} " " vee subb " " slot{'b}

dform band_df : parens :: "prec"[prec_band] :: band{'a; 'b} =
   slot{'a} " " wedge subb " " slot{'b}

dform bimplies_df : parens :: "prec"[prec_bimplies] :: bimplies{'a; 'b} =
   slot{'a} " " Rightarrow subb " " slot{'b}

dform bnot_df : parens :: "prec"[prec_bnot] :: bnot{'a} =
   tneg subb slot{'a}

dform ifthenelse_df : parens :: "prec"[prec_bor] :: ifthenelse{'e1; 'e2; 'e3} =
   szone pushm[0] push_indent `"if" `" " slot{'e1} `" " `"then" hspace
   szone slot{'e2} ezone popm hspace
   push_indent `"else" hspace
   szone slot{'e3} ezone popm popm ezone

dform assert_df : parens :: "prec"[prec_assert] :: "assert"{'t} =
   downarrow slot{'t}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Bool = Bool in Ui ext Ax
 * by boolEquality
 *)
interactive boolEquality {| intro_resource []; eqcd_resource |} 'H :
   sequent ['ext] { 'H >- "bool" = "bool" in univ[i:l] }

interactive boolMember {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- member{univ[i:l]; ."bool"} }

interactive boolType {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "type"{bool} }

(*
 * H >- Unit = Unit in Ui ext Ax
 * by boolEquality
 *)
interactive bool_trueEquality {| intro_resource []; eqcd_resource |} 'H :
  sequent ['ext] { 'H >- btrue = btrue in "bool" }

interactive bool_falseEquality {| intro_resource []; eqcd_resource |} 'H :
   sequent ['ext] { 'H >- bfalse = bfalse in "bool" }

interactive bool_trueMember {| intro_resource [] |} 'H :
  sequent ['ext] { 'H >- member{."bool"; btrue} }

interactive bool_falseMember {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- member{."bool"; bfalse} }

(*
 * H; i:x:Unit; J >- C
 * by boolElimination i
 * H; i:x:Unit; J[it / x] >- C[it / x]
 *)
interactive boolElimination2 {| elim_resource [] |} 'H 'J 'x :
   [main] sequent['ext] { 'H; 'J[btrue] >- 'C[btrue] } -->
   [main] sequent['ext] { 'H; 'J[bfalse] >- 'C[bfalse] } -->
   sequent ['ext] { 'H; x: "bool"; 'J['x] >- 'C['x] }

(*
 * Typing rules for ifthenelse.
 *)
interactive ifthenelse_type2 {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- member{bool; 'e} } -->
   [wf] sequent [squash] { 'H; x: 'e = btrue in bool >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; x: 'e = bfalse in bool >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{ifthenelse{'e; 'A; 'B}} }

(*
 * True is not false.
 *)
interactive boolContradiction1 {| elim_resource [ThinOption thinT] |} 'H 'J :
   sequent ['ext] { 'H; x: btrue = bfalse in bool; 'J['x] >- 'C['x] }

interactive boolContradiction2 {| elim_resource [ThinOption thinT] |} 'H 'J :
   sequent ['ext] { 'H; x: bfalse = btrue in bool; 'J['x] >- 'C['x] }

interactive ifthenelse_equality {| intro_resource []; eqcd_resource |} 'H 'w :
   [wf] sequent [squash] { 'H >- 'e1 = 'e2 in bool } -->
   [wf] sequent [squash] { 'H; w: 'e1 = btrue in bool >- 'x1 = 'x2 in 'T } -->
   [wf] sequent [squash] { 'H; w: 'e1 = bfalse in bool >- 'y1 = 'y2 in 'T } -->
   sequent ['ext] { 'H >- ifthenelse{'e1; 'x1; 'y1} = ifthenelse{'e2; 'x2; 'y2} in 'T }

interactive ifthenelse_member1 {| intro_resource [] |} 'H 'w :
   [wf] sequent [squash] { 'H >- member{."bool"; 'e1} } -->
   [wf] sequent [squash] { 'H; w: 'e1 = btrue in bool >- member{'T; 'x1} } -->
   [wf] sequent [squash] { 'H; w: 'e1 = bfalse in bool >- member{'T; 'y1} } -->
   sequent ['ext] { 'H >- member{'T; ifthenelse{'e1; 'x1; 'y1}} }

(*
 * Squiggle rule.
 *)
interactive boolSqequal 'H :
   sequent [squash] { 'H >- 'x = 'y in bool } -->
   sequent ['ext] { 'H >- Perv!"rewrite"{'x; 'y} }

let d_bool_sqequalT p =
   boolSqequal (Sequent.hyp_count_addr p) p

let bool_sqequal_term1 = << Perv!"rewrite"{'e; btrue} >>
let bool_sqequal_term2 = << Perv!"rewrite"{'e; bfalse} >>
let bool_sqequal_term3 = << Perv!"rewrite"{btrue; 'e} >>
let bool_sqequal_term4 = << Perv!"rewrite"{bfalse; 'e} >>

let intro_resource = Mp_resource.improve intro_resource (bool_sqequal_term1, d_bool_sqequalT)
let intro_resource = Mp_resource.improve intro_resource (bool_sqequal_term2, d_bool_sqequalT)
let intro_resource = Mp_resource.improve intro_resource (bool_sqequal_term3, d_bool_sqequalT)
let intro_resource = Mp_resource.improve intro_resource (bool_sqequal_term4, d_bool_sqequalT)

interactive boolElimination3 {| elim_resource [] |} 'H 'J 'x :
   sequent['ext] { 'H; 'J[btrue] >- 'C[btrue] } -->
   sequent['ext] { 'H; 'J[bfalse] >- 'C[bfalse] } -->
   sequent ['ext] { 'H; x: hide{."bool"}; 'J['x] >- 'C['x] }

(*
 * H >- Ui ext Unit
 * by boolFormation
 *)
interactive boolFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H >- Bool ext btrue
 * by bool_*Formation
 *)
interactive bool_trueFormation 'H :
   sequent ['ext] { 'H >- "bool" }

interactive bool_falseFormation 'H :
   sequent ['ext] { 'H >- "bool" }

(*
 * Membership.
 *)
interactive bfalse_member {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- member{bool; bfalse} }

interactive btrue_member {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- member{bool; btrue} }

interactive ifthenelse_member2 {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- member{bool; 'e1} } -->
   [wf] sequent [squash] { 'H; x: 'e1 = btrue in bool >- member{'T; 'e2} } -->
   [wf] sequent [squash] { 'H; x: 'e1 = bfalse in bool >- member{'T; 'e3} } -->
   sequent ['ext] { 'H >- member{'T; ifthenelse{'e1; 'e2; 'e3}} }

interactive bor_member {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{bool; 't1} } -->
   [wf] sequent [squash] { 'H >- member{bool; 't2} } -->
   sequent ['ext] { 'H >- member{bool; bor{'t1; 't2}} }

interactive band_member {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{bool; 't1} } -->
   [wf] sequent [squash] { 'H >- member{bool; 't2} } -->
   sequent ['ext] { 'H >- member{bool; band{'t1; 't2}} }

interactive bimplies_member {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{bool; 't1} } -->
   [wf] sequent [squash] { 'H >- member{bool; 't2} } -->
   sequent ['ext] { 'H >- member{bool; bimplies{'t1; 't2}} }

interactive bnot_member {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{bool; 'a} } -->
   sequent ['ext] { 'H >- member{bool; bnot{'a}} }

(*
 * Simple assertions.
 *)
interactive assert_type {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{bool; 't} } -->
   sequent ['ext] { 'H >- "type"{."assert"{'t}} }

interactive assert_true {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "assert"{btrue} }

interactive assert_false {| elim_resource [ThinOption thinT] |} 'H 'J :
   sequent ['ext] { 'H; x: "assert"{bfalse}; 'J['x] >- 'C['x] }

(*
 * Substitution.
 *)
interactive bool_subst_concl 'H bind{x. 'C['x]} 'e 'y :
   [wf] sequent [squash] { 'H >- member{bool; 'e} } -->
   [main] sequent ['ext] { 'H; y: "assert"{'e} >- 'C[btrue] } -->
   [main] sequent ['ext] { 'H; y: "assert"{bnot{'e}} >- 'C[bfalse] } -->
   sequent ['ext] { 'H >- 'C['e] }

interactive bool_subst_hyp 'H 'J bind{x. 'A['x]} 'e 'y :
   [wf] sequent [squash] { 'H; x: 'A['e]; 'J['x] >- member{bool; 'e} } -->
   [main] sequent ['ext] { 'H; x: 'A[btrue]; 'J['x]; y: "assert"{'e} >- 'C['x] } -->
   [main] sequent ['ext] { 'H; x: 'A[bfalse]; 'J['x]; y: "assert"{bnot{'e}} >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'A['e]; 'J['x] >- 'C['x] }

interactive bool_ext_equality 'H 'u :
   [wf] sequent [squash] { 'H >- member{bool; 'x} } -->
   [wf] sequent [squash] { 'H >- member{bool; 'y} } -->
   [main] sequent [squash] { 'H; u: "assert"{'x} >- "assert"{'y} } -->
   [main] sequent [squash] { 'H; u: "assert"{'y} >- "assert"{'x} } -->
   sequent ['ext] { 'H >- 'x = 'y in bool }

(*
 * More complex assertions.
 *)
interactive assert_bnot_intro {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- member{bool; 't1} } -->
   [main] sequent [squash] { 'H; x: "assert"{'t1} >- "false" } -->
   sequent ['ext] { 'H >- "assert"{bnot{'t1}} }

interactive assert_bnot_elim {| elim_resource [] |} 'H 'J :
   [wf] sequent [squash] { 'H; 'J[it] >- "assert"{'t} } -->
   sequent ['ext] { 'H; x: "assert"{bnot{'t}}; 'J['x] >- 'C['x] }

interactive assert_magic 'H 'x :
   [wf] sequent [squash] { 'H >- member{bool; 't} } -->
   [wf] sequent [squash] { 'H; x: "assert"{bnot{'t}} >- "false" } -->
   sequent ['ext] { 'H >- "assert"{'t} }

interactive assert_bor_elim {| elim_resource [] |} 'H 'J :
   [wf] sequent [squash] { 'H; x: "assert"{bor{'t1; 't2}}; 'J['x] >- member{bool; 't1} } -->
   [main] sequent ['ext] { 'H; x: "assert"{'t1}; 'J[it] >- 'C[it] } -->
   [main] sequent ['ext] { 'H; x: "assert"{'t2}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{bor{'t1; 't2}}; 'J['x] >- 'C['x] }

interactive assert_band_elim {| elim_resource [] |} 'H 'J 'y 'z :
   [wf] sequent [squash] { 'H; x: "assert"{band{'t1; 't2}}; 'J['x] >- member{bool; 't1} } -->
   [main] sequent ['ext] { 'H; y: "assert"{'t1}; z: "assert"{'t2}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{band{'t1; 't2}}; 'J['x] >- 'C['x] }

interactive assert_bimplies_elim {| elim_resource [] |} 'H 'J :
   [assertion] sequent [squash] { 'H; 'J[it] >- "assert"{'t1} } -->
   [main] sequent ['ext] { 'H; 'J[it]; y: "assert"{'t2} >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{bimplies{'t1; 't2}}; 'J['x] >- 'C['x] }

interactive assert_bor_intro_left {| intro_resource [SelectOption 1] |} 'H :
   [wf] sequent [squash] { 'H >- member{bool; 't2} } -->
   [main] sequent [squash] { 'H >- "assert"{'t1} } -->
   sequent ['ext] { 'H >- "assert"{bor{'t1; 't2}} }

interactive assert_bor_intro_right {| intro_resource [SelectOption 2] |} 'H :
   [wf] sequent [squash] { 'H >- member{bool; 't1} } -->
   [main] sequent [squash] { 'H >- "assert"{'t2} } -->
   sequent ['ext] { 'H >- "assert"{bor{'t1; 't2}} }

interactive assert_band_intro {| intro_resource [] |} 'H :
   [main] sequent [squash] { 'H >- "assert"{'t1} } -->
   [main] sequent [squash] { 'H >- "assert"{'t2} } -->
   sequent ['ext] { 'H >- "assert"{band{'t1; 't2}} }

interactive assert_bimplies_intro {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- member{bool; 't1} } -->
   [main] sequent [squash] { 'H; x: "assert"{'t1} >- "assert"{'t2} } -->
   sequent ['ext] { 'H >- "assert"{bimplies{'t1; 't2}} }

(*
 * Squash elimination on assert.
 *)
interactive assertSquashElim 'H :
   sequent [squash] { 'H >- "assert"{'t} } -->
   sequent ['ext] { 'H >- "assert"{'t} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Standard term.
 *)
let bool_term = << "bool" >>
let btrue_term = << btrue >>
let bfalse_term = << bfalse >>

let assert_term = << "assert"{'t} >>
let assert_opname = opname_of_term assert_term
let mk_assert_term = mk_dep0_term assert_opname
let is_assert_term = is_dep0_term assert_opname
let dest_assert = dest_dep0_term assert_opname

let ifthenelse_term = << ifthenelse{'e1; 'e2; 'e3} >>
let ifthenelse_opname = opname_of_term ifthenelse_term
let mk_ifthenelse_term = mk_dep0_dep0_dep0_term ifthenelse_opname
let is_ifthenelse_term = is_dep0_dep0_dep0_term ifthenelse_opname
let dest_ifthenelse = dest_dep0_dep0_dep0_term ifthenelse_opname

let extBoolT p =
   let v = maybe_new_vars1 p "u" in
      bool_ext_equality (Sequent.hyp_count_addr p) v p

let d_magic_assertT p =
   let v = maybe_new_vars1 p "v" in
      assert_magic (Sequent.hyp_count_addr p) v p

let magicT = d_magic_assertT

(************************************************************************
 * BOOL SPLITTING                                                       *
 ************************************************************************)

(*
 * Split a bool in the conclusion.
 *)
let splitBoolCT a p =
   let x = get_opt_var_arg "z" p in
   let bind =
      try
         let t1 = get_with_arg p in
            if is_bind_term t1 then
               t1
            else
               raise (RefineError ("splitBoolT", StringTermError ("need a \"bind\" term: ", t1)))
      with
         RefineError _ ->
            mk_bind_term x (var_subst (Sequent.concl p) a x)
   in
      bool_subst_concl (Sequent.hyp_count_addr p) bind a x p

(*
 * Split a bool in a hyp.
 *)
let splitBoolHT i a p =
   let _, t1 = Sequent.nth_hyp p i in
   let z = get_opt_var_arg "z" p in
   let bind =
      try
         let b = get_with_arg p in
            if is_bind_term b then
               b
            else
               raise (RefineError ("splitBoolT", StringTermError ("need a \"bind\" term: ", b)))
      with
         RefineError _ ->
            mk_bind_term z (var_subst t1 a z)
   in
   let j, k = Sequent.hyp_indices p i in
      bool_subst_hyp j k bind a z p

let splitBoolT t i =
   if i = 0 then
      splitBoolCT t
   else
      splitBoolHT i t

(*
 * Split ifthenelse.
 *)
let search_ifthenelse goal =
   let rec search addrs vars addr goal =
      if is_ifthenelse_term goal then
         let t, _, _ = dest_ifthenelse goal in
            if is_some_var_free_list vars [t] then
               search_term addrs vars addr goal
            else
               search_term ((addr, t) :: addrs) vars addr goal
      else
         search_term addrs vars addr goal
   and search_term addrs vars addr goal =
      let { term_terms = bterms } = dest_term goal in
         search_bterms addrs vars (0 :: addr) bterms
   and search_bterms addrs vars addr = function
      bterm :: bterms ->
         let { bvars = bvars; bterm = bterm } = dest_bterm bterm in
         let addrs = search addrs (bvars @ vars) addr bterm in
         let addr =
            match addr with
               i :: t ->
                  succ i :: t
             | [] ->
                  raise (Failure "search_ifthenelse: empty address")
         in
            search_bterms addrs vars addr bterms
    | [] ->
         addrs
   in
      search [] [] [] goal

(*
 * Filter out all the addresses for the term.
 *)
let rec filter_ifthenelse t = function
   (addr, t') :: tl ->
      if alpha_equal t t' then
         List.rev addr :: filter_ifthenelse t tl
      else
         filter_ifthenelse t tl
 | [] ->
      []

(*
 * Reduce the ifthenelse true cases.
 *)
let rec reduce_ite_trueC = function
   addr :: addrs ->
      addrC addr reduce_ifthenelse_true andthenC reduce_ite_trueC addrs
 | [] ->
      idC

let rec reduce_ite_falseC = function
   addr :: addrs ->
      addrC addr reduce_ifthenelse_false andthenC reduce_ite_falseC addrs
 | [] ->
      idC

(*
 * Split the ifthenelse.
 *)
let splitITE i p =
   let t =
      if i = 0 then
         Sequent.concl p
      else
         let _, t = Sequent.nth_hyp p i in
            t
   in
   let addrs = search_ifthenelse t in
   let t =
      try get_with_arg p with
         RefineError _ ->
            match addrs with
               (_, t) :: _ ->
                  t
             | [] ->
                  raise (RefineError ("search_ifthenelse", StringError "no free ifthenelse"))
   in
   let addrs = filter_ifthenelse t addrs in
   let _ =
      if addrs = [] then
         raise (RefineError ("splitITE", StringTermError ("no condition", t)))
   in
      (splitBoolT t i
       thenLT [addHiddenLabelT "wf";
               rw (reduce_ite_trueC addrs) i;
               rw (reduce_ite_falseC addrs) i]) p

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of unit.
 *)
let inf_bool _ decl _ = decl, univ1_term

let typeinf_resource = Mp_resource.improve typeinf_resource (bool_term, inf_bool)

(*
 * Type of an equality is the type of the equality type.
 *)
let inf_btrue _ decl _ = decl, bool_term
let inf_bfalse _ decl _ = decl, bool_term

let typeinf_resource = Mp_resource.improve typeinf_resource (btrue_term, inf_btrue)
let typeinf_resource = Mp_resource.improve typeinf_resource (bfalse_term, inf_bfalse)

(************************************************************************
 * AUTO TACTIC                                                          *
 ************************************************************************)

let squash_assertT p =
   let _ =
      match Sequent.args p with
         [ext] ->
            if is_squash_term ext then
               raise (RefineError ("squash_assertT", StringError "already squashed"))
       | _ ->
            ()
   in
      assertSquashElim (Sequent.hyp_count_addr p) p

let auto_resource =
   Mp_resource.improve auto_resource (**)
      { auto_name = "bool_squash_assertT";
        auto_prec = trivial_prec;
        auto_tac = auto_wrap squash_assertT
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
