(*
 * Intersection type.
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
include Itt_set
include Itt_rfun
include Itt_logic

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

open Itt_equal
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_isect%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "isect"{'A; x. 'B['x]}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform isect_df1 : mode[prl] :: (isect x: 'A. 'B) =
   cap slot{'x} `":" slot{'A} `"." slot{'B}
dform isect_df2 : mode[src] :: (isect x: 'A. 'B) =
   `"isect " slot{'x} `":" slot{'A} `"." slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext isect x: A. B[x]
 * by intersectionFormation x A
 * H >- A = A in Ui
 * H, x: A >- Ui ext B[x]
 *)
prim intersectionFormation 'H 'x 'A :
   [wf] sequent [squash] { 'H >- 'A = 'A in univ[i:l] } -->
   ('B['x] : sequent ['ext] { 'H; x: 'A >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   isect x: 'A. 'B['x]

(*
 * H >- isect x1:A1. B1[x1] = isect x2:A2. B2[x2] in Ui
 * by intersectionEquality y
 * H >- A1 = A2 in Ui
 * H, y: A1 >- B1[y] = B2[y] in Ui
 *)
prim intersectionEquality {| intro_resource []; eqcd_resource |} 'H 'y :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent ['ext] { 'H >- isect x1: 'A1. 'B1['x1] = isect x2: 'A2. 'B2['x2] in univ[i:l] } =
   it

prim intersectionType {| intro_resource [] |} 'H 'y :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- "type"{."isect"{'A; x. 'B['x]}} } =
   it

(*
 * H >- isect x: A. B[x] ext b[it]
 * by intersectionMemberFormation z
 * H >- A = A in type
 * H, z: hide(A) >- B[z] ext b[z]
 *)
prim intersectionMemberFormation {| intro_resource [] |} 'H 'z :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [main] ('b['z] : sequent ['ext] { 'H; z: hide{'A} >- 'B['z] }) -->
   sequent ['ext] { 'H >- isect x: 'A. 'B['x] } =
   'b[it]

(*
 * H >- b1 = b2 in isect x:A. B[x]
 * by intersectionMemberEquality z
 * H >- A = A in type
 * H, z: A >- b1 = b2 in B[z]
 *)
prim intersectionMemberEquality {| intro_resource []; eqcd_resource |} 'H 'z :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; z: 'A >- 'b1 = 'b2 in 'B['z] } -->
   sequent ['ext] { 'H >- 'b1 = 'b2 in isect x: 'A. 'B['x] } =
   it

(*
 * H >- b1 = b2 in B[a]
 * by intersectionMemberCaseEquality (isect x:A. B[x]) a
 * H >- b1 = b2 in isect x:A. B[x]
 * H >- a = a in A
 *)
prim intersectionMemberCaseEquality 'H (isect x: 'A. 'B['x]) 'a :
   [wf] sequent [squash] { 'H >- 'b1 = 'b2 in isect x: 'A. 'B['x] } -->
   [wf] sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'b1 = 'b2 in 'B['a] } =
   it

(*
 * H, x: isect y: A. B[y], J[x] >- T[x] ext t[x, x, it]
 * by intersectionElimination a z v
 * H, x: isect y: A. B[y], J[x] >- a = a in A
 * H, x: isect y: A. B[y], J[x], z: B[a], v: z = f in B[a] >- T[x] ext t[x, y, z]
 *)
prim intersectionElimination {| elim_resource [] |} 'H 'J 'a 'x 'y 'v :
   [wf] sequent [squash] { 'H; x: isect y: 'A. 'B['y]; 'J['x] >- 'a = 'a in 'A } -->
   [main] ('t['x; 'y; 'v] : sequent ['ext] { 'H; x: isect y: 'A. 'B['y]; 'J['x]; z: 'B['a]; v: 'z = 'x in 'B['a] >- 'T['x] }) -->
   sequent ['ext] { 'H; x: isect y: 'A. 'B['y]; 'J['x] >- 'T['x] } =
   't['x; 'x; it]

(*
 * H >- isect a1:A1. B1 <= isect a2:A2. B2
 * by intersectionSubtype
 *
 * H >- A2 <= A1
 * H, a: A1 >- B1[a] <= B2[a]
 *)
prim intersectionSubtype {| intro_resource [] |} 'H 'a :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { 'H >- subtype{ (isect a1:'A1. 'B1['a1]); (isect a2:'A2. 'B2['a2]) } } =
   it

interactive intersectionSubtype2 'H 'y 'a :
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent [squash] { 'H >- subtype{'B['a]; 'T} } -->
   sequent ['ext] { 'H >- subtype{."isect"{'A; x. 'B['x]}; 'T} }

interactive intersectionSubtype3 'H 'x :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- "type"{'C} } -->
   sequent [squash] { 'H; x: 'A >- subtype{'C; 'B['x]} } -->
   sequent ['ext] { 'H >- subtype{'C; ."isect"{'A; x. 'B['x]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let isect_term = << isect x: 'A. 'B['x] >>
let isect_opname = opname_of_term isect_term
let is_isect_term = is_dep0_dep1_term isect_opname
let dest_isect = dest_dep0_dep1_term isect_opname
let mk_isect_term = mk_dep0_dep1_term isect_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of isect.
 *)
let inf_isect f decl t =
   let v, a, b = dest_isect t in
   let decl', a' = f decl a in
   let decl'', b' = f (add_unify_subst v a decl') b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2 0)

let typeinf_resource = Mp_resource.improve typeinf_resource (isect_term, inf_isect)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two intersection types.
 *)
let isect_subtypeT p =
   let a = get_opt_var_arg "x" p in
      (intersectionSubtype (Sequent.hyp_count_addr p) a
       thenT addHiddenLabelT "subtype") p

let sub_resource =
   Mp_resource.improve
   sub_resource
   (DSubtype ([<< isect a1:'A1. 'B1['a1] >>, << isect a2:'A2. 'B2['a2] >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              isect_subtypeT))

let d_isect_subtypeT i p =
   if i = 0 then
      let a = get_with_arg p in
      let concl = Sequent.concl p in
      let v, _, _ = dest_isect concl in
      let v = maybe_new_vars1 p v in
         (intersectionSubtype2 (Sequent.hyp_count_addr p) v a
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  idT]) p
   else
      raise (RefineError ("d_isect_subtypeT", StringError "no elimination form"))

let isect_subtype_term = << subtype{."isect"{'A; x. 'B['x]}; 'T} >>

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
