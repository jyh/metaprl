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
include Itt_logic
include Itt_struct

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tacticals
open Conversionals
open Var

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
prim_rw reduce_ifthenelse_true : ifthenelse{btrue; 'e1; 'e2} <--> 'e1
prim_rw reduce_ifthenelse_false : ifthenelse{bfalse; 'e1; 'e2} <--> 'e2
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

dform bool_df : mode[prl] :: bool =
   `"Bool"

dform btrue_df : mode[prl] :: btrue =
   `"true"

dform bfalse_df : mode[prl] :: bfalse =
   `"false"

dform bor_df : mode[prl] :: parens :: "prec"[prec_bor] :: bor{'a; 'b} =
   slot{'a} " " vee subb " " slot{'b}

dform band_df : mode[prl] :: parens :: "prec"[prec_band] :: band{'a; 'b} =
   slot{'a} " " wedge subb " " slot{'b}

dform bimplies_df : mode[prl] :: parens :: "prec"[prec_bimplies] :: bimplies{'a; 'b} =
   slot{'a} " " Rightarrow subb " " slot{'b}

dform bnot_df : mode[prl] :: parens :: "prec"[prec_bnot] :: bnot{'a} =
   tneg subb slot{'a}

dform ifthenelse_df : mode[prl] :: parens :: "prec"[prec_bor] :: ifthenelse{'e1; 'e2; 'e3} =
   pushm[0] szone push_indent `"if" `" " slot{'e1} `" " `"then" hspace
   szone slot{'e2} ezone popm hspace
   push_indent `"else" hspace
   szone slot{'e3} ezone popm popm

dform assert_df : mode[prl] :: parens :: "prec"[prec_assert] :: "assert"{'t} =
   downarrow slot{'t}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Bool = Bool in Ui ext Ax
 * by boolEquality
 *)
interactive boolEquality 'H : :
   sequent ['ext] { 'H >- "bool" = "bool" in univ[@i:l] }

interactive boolType 'H : :
   sequent ['ext] { 'H >- "type"{bool} }

(*
 * H >- Unit = Unit in Ui ext Ax
 * by boolEquality
 *)
interactive bool_trueEquality 'H : :
  sequent ['ext] { 'H >- btrue = btrue in "bool" }

interactive bool_falseEquality 'H : :
   sequent ['ext] { 'H >- bfalse = bfalse in "bool" }

(*
 * H; i:x:Unit; J >- C
 * by boolElimination i
 * H; i:x:Unit; J[it / x] >- C[it / x]
 *)
interactive boolElimination2 'H 'J 'x :
   sequent['ext] { 'H; 'J[btrue] >- 'C[btrue] } -->
   sequent['ext] { 'H; 'J[bfalse] >- 'C[bfalse] } -->
   sequent ['ext] { 'H; x: "bool"; 'J['x] >- 'C['x] }

(*
 * Typing rules for ifthenelse.
 *)
interactive ifthenelse_type 'H 'x :
   sequent [squash] { 'H >- 'e = 'e in bool } -->
   sequent [squash] { 'H; x: 'e = btrue in bool >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'e = bfalse in bool >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{ifthenelse{'e; 'A; 'B}} }

(*
 * True is not false.
 *)
interactive boolContradiction1 'H 'J : :
   sequent ['ext] { 'H; x: btrue = bfalse in bool; 'J['x] >- 'C['x] }

interactive boolContradiction2 'H 'J : :
   sequent ['ext] { 'H; x: bfalse = btrue in bool; 'J['x] >- 'C['x] }

interactive ifthenelse_equality 'H 'w :
   sequent [squash] { 'H >- 'e1 = 'e2 in bool } -->
   sequent [squash] { 'H; w: 'e1 = btrue in bool >- 'x1 = 'x2 in 'T } -->
   sequent [squash] { 'H; w: 'e1 = bfalse in bool >- 'y1 = 'y2 in 'T } -->
   sequent ['ext] { 'H >- ifthenelse{'e1; 'x1; 'y1} = ifthenelse{'e2; 'x2; 'y2} in 'T }

(*
 * Squiggle rule.
 *)
interactive boolSqequal 'H :
   sequent [squash] { 'H >- 'x = 'y in bool } -->
   sequent ['ext] { 'H >- Perv!"rewrite"{'x; 'y} }

interactive boolElimination3 'H 'J 'x :
   sequent['ext] { 'H; 'J[btrue] >- 'C[btrue] } -->
   sequent['ext] { 'H; 'J[bfalse] >- 'C[bfalse] } -->
   sequent ['ext] { 'H; x: hide{."bool"}; 'J['x] >- 'C['x] }

(*
 * H >- Ui ext Unit
 * by boolFormation
 *)
interactive boolFormation 'H : :
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- Bool ext btrue
 * by bool_*Formation
 *)
interactive bool_trueFormation 'H : :
   sequent ['ext] { 'H >- "bool" }

interactive bool_falseFormation 'H : :
   sequent ['ext] { 'H >- "bool" }

(*
 * Membership.
 *)
interactive bfalse_member 'H : :
   sequent ['ext] { 'H >- member{bool; bfalse} }

interactive btrue_member 'H : :
   sequent ['ext] { 'H >- member{bool; btrue} }

interactive ifthenelse_member 'H 'x :
   sequent [squash] { 'H >- member{bool; 'e1} } -->
   sequent [squash] { 'H; x: 'e1 = btrue in bool >- member{'T; 'e2} } -->
   sequent [squash] { 'H; x: 'e1 = bfalse in bool >- member{'T; 'e3} } -->
   sequent ['ext] { 'H >- member{'T; ifthenelse{'e1; 'e2; 'e3}} }

interactive bor_member 'H :
   sequent [squash] { 'H >- member{bool; 't1} } -->
   sequent [squash] { 'H >- member{bool; 't2} } -->
   sequent ['ext] { 'H >- member{bool; bor{'t1; 't2}} }

interactive band_member 'H :
   sequent [squash] { 'H >- member{bool; 't1} } -->
   sequent [squash] { 'H >- member{bool; 't2} } -->
   sequent ['ext] { 'H >- member{bool; band{'t1; 't2}} }

interactive bimplies_member 'H :
   sequent [squash] { 'H >- member{bool; 't1} } -->
   sequent [squash] { 'H >- member{bool; 't2} } -->
   sequent ['ext] { 'H >- member{bool; bimplies{'t1; 't2}} }

interactive bnot_member 'H :
   sequent [squash] { 'H >- member{bool; 'a} } -->
   sequent ['ext] { 'H >- member{bool; bnot{'a}} }

(*
 * Simple assertions.
 *)
interactive assert_type 'H :
   sequent [squash] { 'H >- member{bool; 't} } -->
   sequent ['ext] { 'H >- "type"{."assert"{'t}} }

interactive assert_true 'H : :
   sequent ['ext] { 'H >- "assert"{btrue} }

interactive assert_false 'H 'J : :
   sequent ['ext] { 'H; x: "assert"{bfalse}; 'J['x] >- 'C['x] }

(*
 * Substitution.
 *)
interactive bool_subst_concl 'H bind{x. 'C['x]} 'e 'y :
   sequent [squash] { 'H >- member{bool; 'e} } -->
   sequent ['ext] { 'H; y: "assert"{'e} >- 'C[btrue] } -->
   sequent ['ext] { 'H; y: "assert"{bnot{'e}} >- 'C[bfalse] } -->
   sequent ['ext] { 'H >- 'C['e] }

interactive bool_subst_hyp 'H 'J bind{x. 'A['x]} 'e 'y :
   sequent [squash] { 'H; x: 'A['e]; 'J['x] >- member{bool; 'e} } -->
   sequent ['ext] { 'H; x: 'A[btrue]; 'J['x]; y: "assert"{'e} >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'A[bfalse]; 'J['x]; y: "assert"{bnot{'e}} >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'A['e]; 'J['x] >- 'C['x] }

interactive bool_ext_equality 'H 'u :
   sequent [squash] { 'H >- member{bool; 'x} } -->
   sequent [squash] { 'H >- member{bool; 'y} } -->
   sequent [squash] { 'H; u: "assert"{'x} >- "assert"{'y} } -->
   sequent [squash] { 'H; u: "assert"{'y} >- "assert"{'x} } -->
   sequent ['ext] { 'H >- 'x = 'y in bool }

(*
 * More complex assertions.
 *)
interactive assert_bnot_intro 'H 'x :
   sequent [squash] { 'H >- member{bool; 't1} } -->
   sequent [squash] { 'H; x: "assert"{'t1} >- "false" } -->
   sequent ['ext] { 'H >- "assert"{bnot{'t1}} }

interactive assert_bnot_elim 'H 'J :
   sequent [squash] { 'H; 'J[it] >- "assert"{'t} } -->
   sequent ['ext] { 'H; x: "assert"{bnot{'t}}; 'J['x] >- 'C['x] }

interactive assert_magic 'H 'x :
   sequent [squash] { 'H >- member{bool; 't} } -->
   sequent [squash] { 'H; x: "assert"{bnot{'t}} >- "false" } -->
   sequent ['ext] { 'H >- "assert"{'t} }

interactive assert_bor_elim 'H 'J :
   sequent [squash] { 'H; x: "assert"{bor{'t1; 't2}}; 'J['x] >- member{bool; 't1} } -->
   sequent ['ext] { 'H; x: "assert"{'t1}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{'t2}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{bor{'t1; 't2}}; 'J['x] >- 'C['x] }

interactive assert_band_elim 'H 'J 'y 'z :
   sequent [squash] { 'H; x: "assert"{band{'t1; 't2}}; 'J['x] >- member{bool; 't1} } -->
   sequent ['ext] { 'H; y: "assert"{'t1}; z: "assert"{'t2}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{band{'t1; 't2}}; 'J['x] >- 'C['x] }

interactive assert_bimplies_elim 'H 'J :
   sequent [squash] { 'H; 'J[it] >- "assert"{'t1} } -->
   sequent ['ext] { 'H; 'J[it]; y: "assert"{'t2} >- 'C[it] } -->
   sequent ['ext] { 'H; x: "assert"{bimplies{'t1; 't2}}; 'J['x] >- 'C['x] }

interactive assert_bor_intro_left 'H :
   sequent [squash] { 'H >- member{bool; 't2} } -->
   sequent [squash] { 'H >- "assert"{'t1} } -->
   sequent ['ext] { 'H >- "assert"{bor{'t1; 't2}} }

interactive assert_bor_intro_right 'H :
   sequent [squash] { 'H >- member{bool; 't1} } -->
   sequent [squash] { 'H >- "assert"{'t2} } -->
   sequent ['ext] { 'H >- "assert"{bor{'t1; 't2}} }

interactive assert_band_intro 'H :
   sequent [squash] { 'H >- "assert"{'t1} } -->
   sequent [squash] { 'H >- "assert"{'t2} } -->
   sequent ['ext] { 'H >- "assert"{band{'t1; 't2}} }

interactive assert_bimplies_intro 'H 'x :
   sequent [squash] { 'H >- member{bool; 't1} } -->
   sequent [squash] { 'H; x: "assert"{'t1} >- "assert"{'t2} } -->
   sequent ['ext] { 'H >- "assert"{bimplies{'t1; 't2}} }

(*
 * Squash elimination on assert.
 *)
interactive assertSquashElim 'H :
   sequent [squash] { 'H >- "assert"{'t} } -->
   sequent ['ext] { 'H >- "assert"{'t} }

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
   [<< ifthenelse{btrue; 'e1; 'e2} >>, reduce_ifthenelse_true;
    << ifthenelse{bfalse; 'e1; 'e2} >>, reduce_ifthenelse_false;
    << bnot{btrue} >>, reduce_bnot_true;
    << bnot{bfalse} >>, reduce_bnot_false;
    << bor{btrue; 'e1} >>, reduce_bor_true;
    << bor{bfalse; 'e1} >>, reduce_bor_false;
    << band{btrue; 'e1} >>, reduce_band_true;
    << band{bfalse; 'e1} >>, reduce_band_false;
    << bimplies{btrue; 'e1} >>, reduce_bimplies_true;
    << bimplies{bfalse; 'e1} >>, reduce_bimplies_false]

let reduce_resource = add_reduce_info reduce_resource reduce_info

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

(*
 * Tactic wrapper.
 *)
let wrap_intro_addr tac i p =
   wrap_intro (tac (Sequent.hyp_count_addr p)) i p

let wrap_elim_addr tac i p =
   if i = 0 then
      raise (RefineError ("Itt_bool.wrap_elim_addr", StringError "no introduction form"))
   else
      let j, k = Sequent.hyp_indices p i in
         tac j k p

(*
 * D
 *)
let d_boolT i p =
   if i = 0 then
       bool_trueFormation (Sequent.hyp_count_addr p) p
    else
       let j, k = Sequent.hyp_indices p i in
       let v, _ = Sequent.nth_hyp p i in
          (boolElimination2 j k v
           thenLT [addHiddenLabelT "true case";
                   addHiddenLabelT "false case"]) p

let d_resource = Mp_resource.improve d_resource (bool_term, d_boolT)

let d_bool_hideT i p =
   if i = 0 then
      raise (RefineError ("d_bool_hideT", StringError "no introduction form"))
   else
       let j, k = Sequent.hyp_indices p i in
       let v, _ = Sequent.nth_hyp p i in
          (boolElimination3 j k v
           thenLT [addHiddenLabelT "true case";
                   addHiddenLabelT "false case"]) p

let bool_hide_term = << hide{bool} >>

let d_resource = Mp_resource.improve d_resource (bool_hide_term, d_bool_hideT)

let d_bool_typeT i p =
   if i = 0 then
      boolType (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_bool_trueT", StringError "no elimination form"))

let bool_type_term = << "type"{bool} >>

let d_resource = Mp_resource.improve d_resource (bool_type_term, d_bool_typeT)

(*
 * EqCD.
 *)
let eqcd_boolT p =
   let count = Sequent.hyp_count_addr p in
      boolEquality count p

let eqcd_btrueT p =
   let count = Sequent.hyp_count_addr p in
      bool_trueEquality count p

let eqcd_bfalseT p =
   let count = Sequent.hyp_count_addr p in
      bool_falseEquality count p

let eqcd_resource = Mp_resource.improve eqcd_resource (bool_term, eqcd_boolT)
let eqcd_resource = Mp_resource.improve eqcd_resource (btrue_term, eqcd_btrueT)
let eqcd_resource = Mp_resource.improve eqcd_resource (bfalse_term, eqcd_bfalseT)

let bool_equal_term = << bool = bool in univ[@i:l] >>
let btrue_equal_term = << btrue = btrue in bool >>
let bfalse_equal_term = << bfalse = bfalse in bool >>

let d_resource = Mp_resource.improve d_resource (bool_equal_term, d_wrap_eqcd eqcd_boolT)
let d_resource = Mp_resource.improve d_resource (btrue_equal_term, d_wrap_eqcd eqcd_btrueT)
let d_resource = Mp_resource.improve d_resource (bfalse_equal_term, d_wrap_eqcd eqcd_bfalseT)

let extBoolT p =
   let v = maybe_new_vars1 p "u" in
      (bool_ext_equality (Sequent.hyp_count_addr p) v
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "wf";
               addHiddenLabelT "assertion";
               addHiddenLabelT "assertion"]) p

(*
 * Membership.
 *)
let member_info =
   [<< member{bool; btrue} >>, btrue_member;
    << member{bool; bfalse} >>, bfalse_member;
    << member{bool; bor{'a; 'b}} >>, bor_member;
    << member{bool; band{'a; 'b}} >>, band_member;
    << member{bool; bimplies{'a; 'b}} >>, bimplies_member;
    << member{bool; bnot{'a}} >>, bnot_member]

let d_resource =
   let rec add_info dr = function
      (t, tac) :: tl ->
         add_info (Mp_resource.improve dr (t, wrap_intro_addr tac)) tl
    | [] ->
         dr
   in
      add_info d_resource member_info

let d_ifthenelse_memberT p =
   let v = maybe_new_vars1 p "v" in
      ifthenelse_member (Sequent.hyp_count_addr p) v p

let ifthenelse_member_term = << member{'T; ifthenelse{'e1; 'e2; 'e3}} >>

let d_resource = Mp_resource.improve d_resource (ifthenelse_member_term, wrap_intro d_ifthenelse_memberT)

(*
 * Assertions.
 *)
let d_bnot_assertT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         (assert_bnot_intro (Sequent.hyp_count_addr p) v
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
   else
      let j, k = Sequent.hyp_indices p i in
         (assert_bnot_elim j k
          thenT addHiddenLabelT "main") p

let d_magic_assertT p =
   let v = maybe_new_vars1 p "v" in
      (assert_magic (Sequent.hyp_count_addr p) v
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "main"]) p

let magicT = d_magic_assertT

let d_bor_assertT i p =
   if i = 0 then
      let tac =
         if get_sel_arg p = 1 then
            assert_bor_intro_left
         else
            assert_bor_intro_right
      in
         (tac (Sequent.hyp_count_addr p)
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
   else
      let j, k = Sequent.hyp_indices p i in
         (assert_bor_elim j k
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main";
                  addHiddenLabelT "main"]) p

let d_band_assertT i p =
   if i = 0 then
      (assert_band_intro (Sequent.hyp_count_addr p)
       thenT addHiddenLabelT "main") p
   else
      let j, k = Sequent.hyp_indices p i in
      let u, v = maybe_new_vars2 p "u" "v" in
         (assert_band_elim j k u v
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p

let d_bimplies_assertT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "x" in
         (assert_bimplies_intro (Sequent.hyp_count_addr p) v
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
   else
      let j, k = Sequent.hyp_indices p i in
         (assert_bimplies_elim j k
          thenT addHiddenLabelT "main") p

let assert_info =
   [<< "assert"{btrue} >>, wrap_intro_addr assert_true;
    << "assert"{bfalse} >>, wrap_elim_addr assert_false;
    << "assert"{bnot{'t}} >>, d_bnot_assertT;
    << "assert"{bor{'t1; 't2}} >>, d_bor_assertT;
    << "assert"{band{'t1; 't2}} >>, d_band_assertT;
    << "assert"{bimplies{'t1; 't2}} >>, d_bimplies_assertT]

let d_resource =
   let rec add_info dr = function
      (t, tac) :: tl ->
         add_info (Mp_resource.improve dr (t, tac)) tl
    | [] ->
         dr
   in
      add_info d_resource assert_info

(*
 * Ifthenelse.
 *)
let d_ifthenelse_typeT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         (ifthenelse_type (Sequent.hyp_count_addr p) v
          thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_ifthenelse_typeT", StringError "no elimination form"))

let ifthenelse_type_term = << "type"{ifthenelse{'e1; 'e2; 'e3}} >>

let d_resource = Mp_resource.improve d_resource (ifthenelse_type_term, d_ifthenelse_typeT)

let eqcd_ifthenelseT p =
   let v = maybe_new_vars1 p "v" in
      (ifthenelse_equality (Sequent.hyp_count_addr p) v
       thenT addHiddenLabelT "wf") p

let ifthenelse_term = << ifthenelse{'e1; 'e2; 'e3} >>

let eqcd_resource = Mp_resource.improve eqcd_resource (ifthenelse_term, eqcd_ifthenelseT)

let ifthenelse_equal_term = << ifthenelse{'a1; 'b1; 'c1} = ifthenelse{'a2; 'b2; 'c2} in 'T >>

let d_resource = Mp_resource.improve d_resource (ifthenelse_equal_term, d_wrap_eqcd eqcd_ifthenelseT)

(*
 * Contradiction.
 *)
let d_bool_contradiction1T i p =
   if i = 0 then
      raise (RefineError ("d_bool_contradiction1T", StringError "no introduction form"))
   else
      let j, k = Sequent.hyp_indices p i in
         boolContradiction1 j k p

let d_bool_contradiction2T i p =
   if i = 0 then
      raise (RefineError ("d_bool_contradiction1T", StringError "no introduction form"))
   else
      let j, k = Sequent.hyp_indices p i in
         boolContradiction2 j k p

let bool_contradiction1_term = << btrue = bfalse in bool >>
let bool_contradiction2_term = << bfalse = btrue in bool >>

let d_resource = Mp_resource.improve d_resource (bool_contradiction1_term, d_bool_contradiction1T)
let d_resource = Mp_resource.improve d_resource (bool_contradiction2_term, d_bool_contradiction2T)

(*
 * Assertions.
 *)
let d_true_typeT p =
   assert_type (Sequent.hyp_count_addr p) p

let true_type_term = << "type"{."assert"{'T}} >>

let d_resource = Mp_resource.improve d_resource (true_type_term, wrap_intro d_true_typeT)

(************************************************************************
 * BOOL SPLITTING                                                       *
 ************************************************************************)

(*
 * Sqequal.
 *)
let d_bool_sqequalT i p =
   if i = 0 then
      boolSqequal (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_bool_sqequalT", StringError "no elimination form"))

let bool_sqequal_term1 = << Perv!"rewrite"{'e; btrue} >>
let bool_sqequal_term2 = << Perv!"rewrite"{'e; bfalse} >>
let bool_sqequal_term3 = << Perv!"rewrite"{btrue; 'e} >>
let bool_sqequal_term4 = << Perv!"rewrite"{bfalse; 'e} >>

let d_resource = Mp_resource.improve d_resource (bool_sqequal_term1, d_bool_sqequalT)
let d_resource = Mp_resource.improve d_resource (bool_sqequal_term2, d_bool_sqequalT)
let d_resource = Mp_resource.improve d_resource (bool_sqequal_term3, d_bool_sqequalT)
let d_resource = Mp_resource.improve d_resource (bool_sqequal_term4, d_bool_sqequalT)

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
      (bool_subst_concl (Sequent.hyp_count_addr p) bind a x
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "true case";
               addHiddenLabelT "false case"]) p

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
      (bool_subst_hyp j k bind a z
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "true case";
               addHiddenLabelT "false case"]) p

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
            if is_free_var_list vars [t] then
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
