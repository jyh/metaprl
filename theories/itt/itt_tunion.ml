(*
 * A normal set-style union of types.
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
include Itt_set

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Mp_resource

open Tacticals
open Var

open Itt_equal

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare tunion{'A; x. 'B['x]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_tunion

dform isect_df : mode[prl] :: parens :: "prec"[prec_tunion] :: tunion{'A; x. 'B} =
   cup slot{'x} `":" slot{'A} `"." slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Proof of Ui
 *)
prim tunionFormation 'H 'x 'A :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   ('B['x] : sequent ['ext] { 'H; x: 'A >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   tunion{'A; x. 'B['x]}

(*
 * Typehood.
 *)
prim tunionEquality 'H 'x :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[@i:l] } -->
   sequent ['ext] { 'H >- tunion{'A1; x1. 'B1['x1]} = tunion{'A2; x2. 'B2['x2] } in univ[@i:l] } =
   it

prim tunionType 'H 'y :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- "type"{tunion{'A; x. 'B['x]}} } =
   it

(*
 * Membership.
 *)
prim tunionMemberEquality 'H 'a 'y :
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent [squash] { 'H >- 'x1 = 'x2 in 'B['a] } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in tunion{'A; x. 'B['x]} } =
   it

prim tunionMemberFormation 'H 'y 'a :
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   ('t : sequent ['ext] { 'H >- 'B['a] }) -->
   sequent ['ext] { 'H >- tunion{'A; x. 'B['x]} } =
   't

(*
 * Elimination.
 *)
prim tunionElimination 'H 'J 'x 'w 'z 'w2 :
   ('t['z; 'w2] : sequent ['ext] { 'H; x: tunion{'A; y. 'B['y]}; 'J['x]; w: hide{'A}; z: 'B['w]; w2: 'z = 'x in tunion{'A; y. 'B['y]} >- 'C['x] }) -->
   sequent ['ext] { 'H; x: tunion{'A; y. 'B['y]}; 'J['x] >- 'C['x] } =
   't['x; it]

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let tunion_term = << tunion{'A; x. 'B['x]} >>
let tunion_opname = opname_of_term tunion_term
let mk_tunion_term = mk_dep0_dep1_term tunion_opname
let is_tunion_term = is_dep0_dep1_term tunion_opname
let dest_tunion = dest_dep0_dep1_term tunion_opname

(*
 * D tactic.
 *)
let d_tunionT i p =
   if i = 0 then
      let x = get_with_arg p in
      let union = Sequent.concl p in
      let v, _, _ = dest_tunion union in
      let v = maybe_new_vars1 p v in
         (tunionMemberFormation (Sequent.hyp_count_addr p) v x
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
   else
      let u, v, w = maybe_new_vars3 p "u" "v" "w" in
      let j, k = Sequent.hyp_indices p i in
      let x, _ = Sequent.nth_hyp p i in
         tunionElimination j k x u v w p

let d_resource = Mp_resource.improve d_resource (tunion_term, d_tunionT)

(*
 * Typehood.
 *)
let d_tunion_typeT i p =
   if i = 0 then
      let union = Sequent.concl p in
      let union = dest_type_term union in
      let v, _, _ = dest_tunion union in
      let v = maybe_new_vars1 p v in
         tunionType (Sequent.hyp_count_addr p) v p
   else
      raise (RefineError ("d_union_typeT", StringError "no elimination form"))

let tunion_type_term = << "type"{tunion{'A; x. 'B['x]}} >>

let d_resource = Mp_resource.improve d_resource (tunion_type_term, d_tunion_typeT)

(*
 * Membership.
 *)
let d_tunion_memT i p =
   if i = 0 then
      let x = get_with_arg p in
      let concl = Sequent.concl p in
      let union, _, _ = dest_equal concl in
      let v, _, _ = dest_tunion union in
      let v = maybe_new_vars1 p v in
         (tunionMemberEquality (Sequent.hyp_count_addr p) x v
          thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_tunion_memT", StringError "no elimination form"))

let tunion_mem_term = << 'x = 'y in tunion{'A; z. 'B['z]} >>

let d_resource = Mp_resource.improve d_resource (tunion_mem_term, d_tunion_memT)

(*
 * Equality.
 *)
let eqcd_tunionT p =
   let equal = Sequent.concl p in
   let _, union, _ = dest_equal equal in
   let v, _, _ = dest_tunion union in
   let v = maybe_new_vars1 p v in
      tunionEquality (Sequent.hyp_count_addr p) v p

let eqcd_resource = Mp_resource.improve eqcd_resource (tunion_term, eqcd_tunionT)

let eqcd_tunion_term = << tunion{'A1; x1. 'B1['x1]} = tunion{'A2; x2. 'B2['x2]} in univ[@i:l] >>

let d_resource = Mp_resource.improve d_resource (eqcd_tunion_term, d_wrap_eqcd eqcd_tunionT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
