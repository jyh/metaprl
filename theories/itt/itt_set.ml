(*
 * Set type.
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

include Itt_squash
include Itt_equal
include Itt_unit
include Itt_subtype
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

open Sequent
open Tacticals
open Var

open Itt_squash
open Itt_struct
open Itt_equal
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_set%t" eflush

(* debug_string DebugLoad "Loading itt_set..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare set{'A; x. 'B['x]}
declare hide{'A}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform set_df1 : mode[prl] :: set{'A; x. 'B} =
   pushm[3] `"{ " bvar{'x} `":" slot{'A} `" | " slot{'B} `"}" popm

dform hide_df1 : mode[prl] :: hide{'A} = "[" 'A "]"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext { a:A | B }
 * by setFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
prim setFormation 'H 'a 'A :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] }
   ('B['a] : sequent ['ext] { 'H; a: 'A >- univ[@i:l] }) :
   sequent ['ext] { 'H >- univ[@i:l] } =
   { a: 'A | 'B['a] }

(*
 * H >- { a1:A1 | B1[a1] } = { a2:A2 | B2[a2] } in Ui
 * by setEquality x
 *
 * H >- A1 = A2 in Ui
 * H, x: A1 >- B1[x] = B2[x] in Ui
 *)
prim setEquality 'H 'x :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] }
   sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[@i:l] } :
   sequent ['ext] { 'H >- { a1:'A1 | 'B1['a1] } = { a2:'A2 | 'B2['a2] } in univ[@i:l] } = it

prim setType 'H 'x :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H; x: 'A1 >- "type"{'B1['x]} } -->
   sequent ['ext] { 'H >- "type"{.{ a1:'A1 | 'B1['a1] }} } =
   it

(*
 * H >- { a:A | B[a] } ext a
 * by setMemberFormation Ui a z
 *
 * H >- a = a in A
 * H >- B[a]
 * H, z: A >- B[z] = B[z] in Ui
 *)
prim setMemberFormation 'H 'a 'z :
   sequent [squash] { 'H >- 'a = 'a in 'A }
   sequent ['ext]   { 'H >- 'B['a] }
   sequent [squash] { 'H; z: 'A >- "type"{'B['z]} } :
   sequent ['ext]   { 'H >- { x:'A | 'B['x] } } =
   'a

(*
 * H >- a1 = a2 in { a:A | B }
 * by setMemberEquality Ui x
 *
 * H >- a1 = a2 in A
 * H >- B[a1]
 * H, x: A >- B[x] = B[x] in Ui
 *)
prim setMemberEquality 'H 'x :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A }
   sequent [squash] { 'H >- 'B['a1] }
   sequent [squash] { 'H; x: 'A >- "type"{'B['x]} } :
   sequent ['ext] { 'H >- 'a1 = 'a2 in { a:'A | 'B['a] } } = it

(*
 * H, u: { x:A | B }, J[u] >> T[u] ext t[y]
 * by setElimination2 y v z
 * H, u: { x:A | B }, y: A; v: hide(B[y]); J[y] >> T[y]
 *)
prim setElimination 'H 'J 'u 'v :
   ('t : sequent [it; 'prop] { 'H; u: 'A; v: hide{'B['u]}; 'J['u] >- 'T['u] }) -->
   sequent [it; 'prop] { 'H; u: { x:'A | 'B['x] }; 'J['u] >- 'T['u] } =
   't

(*
 * Subtyping.
 *)
prim set_subtype 'H :
   sequent [squash] { 'H >- "type"{ { a: 'A | 'B['a] } } } -->
   sequent ['ext] { 'H >- subtype{ { a: 'A | 'B['a] }; 'A } } =
   it

(*
 * Equalities can be unhidden.
 *)
prim unhide_equal 'H 'J 'u :
   ('t['u] : sequent [squash] { 'H; u: 'x = 'y in 'A; 'J['u] >- 'C['u] }) -->
   sequent ['ext] { 'H; u: hide{('x = 'y in 'A)}; 'J['u] >- 'C['u] } =
   't[it]

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let set_term = << { a: 'A | 'B['x] } >>
let set_opname = opname_of_term set_term
let mk_set_term = mk_dep0_dep1_term set_opname
let is_set_term = is_dep0_dep1_term set_opname
let dest_set = dest_dep0_dep1_term set_opname

(*
 * D
 *)
let d_set i p =
   if i = 0 then
      let t =
         try get_with_arg p with
            Not_found ->
               raise (RefineError ("d_set", StringError "requires an argument"))
      in
      let v = get_opt_var_arg "z" p in
         setMemberFormation (Sequent.hyp_count_addr p) t v p
   else
      let u, _ = Sequent.nth_hyp p i in
      let v = maybe_new_vars1 p "v" in
      let j, k = Sequent.hyp_indices p i in
         setElimination j k u v p

let d_resource = Mp_resource.improve d_resource (set_term, d_set)

(*
 * EqCD.
 *)
let eqcd_set p =
   let count = Sequent.hyp_count_addr p in
   let v = get_opt_var_arg "x" p in
      setEquality count v p

let eqcd_resource = Mp_resource.improve eqcd_resource (set_term, eqcd_set)

let d_set_typeT p =
   let t = Sequent.concl p in
   let t = dest_type_term t in
   let v, _, _ = dest_set t in
   let v = maybe_new_vars1 p v in
      (setType (Sequent.hyp_count_addr p) v
       thenT addHiddenLabelT "wf") p

let set_type_term = << "type"{.{ a: 'A | 'B['x]}} >>

let d_resource = Mp_resource.improve d_resource (set_type_term, wrap_intro d_set_typeT)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let set_term = << { a: 'A | 'B['a] } >>
let set_opname = opname_of_term set_term
let is_set_term = is_dep0_dep1_term set_opname
let dest_set = dest_dep0_dep1_term set_opname
let mk_set_term = mk_dep0_dep1_term set_opname

let hide_term = << hide{'a} >>
let hide_opname = opname_of_term hide_term
let is_hide_term = is_dep0_term hide_opname
let dest_hide = dest_dep0_term hide_opname
let mk_hide_term = mk_dep0_term hide_opname

(*
 * Unhide an equality.
 *)
let d_hide_equalT i p =
   let j, k = Sequent.hyp_indices p i in
   let u, _ = Sequent.nth_hyp p i in
      unhide_equal j k u p

let hide_equal_term = << hide{.'x = 'y in 'A} >>

let d_resource = Mp_resource.improve d_resource (hide_equal_term, wrap_elim d_hide_equalT)

(*
 * Squash a goal.
 *)
let squashT p =
   if is_squash_goal p then
      idT p
   else
      Sequent.get_tactic_arg p "squash" p

(*
 * EqCD.
 *)
let eqcd_setT p =
   let count = Sequent.hyp_count_addr p in
   let v = get_opt_var_arg "x" p in
      setEquality count v p

let eqcd_resource = Mp_resource.improve eqcd_resource (set_term, eqcd_setT)

(*
 * Membership.
 *)
let d_set_equalT p =
   let t = Sequent.concl p in
   let t, _, _ = dest_equal t in
   let v, _, _ = dest_set t in
   let v = maybe_new_vars1 p v in
      (setMemberEquality (Sequent.hyp_count_addr p) v
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "assertion";
               addHiddenLabelT "wf"]) p

let set_equal_term = << 'x = 'y in { z: 'A | 'B['z] } >>

let d_resource = Mp_resource.improve d_resource (set_equal_term, wrap_intro d_set_equalT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of atom.
 *)
let inf_set f decl t =
   let v, ty, prop = dest_set t in
   let decl', ty' = f decl ty in
   let decl'', prop' = f (add_unify_subst v ty decl') prop in
   let le1, le2 = dest_univ ty', dest_univ prop' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2 0)

let typeinf_resource = Mp_resource.improve typeinf_resource (set_term, inf_set)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

let set_subtypeT p =
   (set_subtype (Sequent.hyp_count_addr p)
    thenT addHiddenLabelT "wf") p

let sub_resource =
   Mp_resource.improve
   sub_resource
   (LRSubtype ([<< { a: 'A | 'B['a] } >>, << 'A >>], set_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
