(*
 * Subtype type.
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
include Itt_struct

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Mp_resource
open Term_dtable

open Var

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent

open Base_dtactic

open Itt_equal
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_subtype%t"

(* debug_string DebugLoad "Loading itt_subtype..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare subtype{'A; 'B}

let subtype_term = << subtype{'A; 'B} >>
let subtype_opname = opname_of_term subtype_term
let is_subtype_term = is_dep0_dep0_term subtype_opname
let dest_subtype = dest_dep0_dep0_term subtype_opname
let mk_subtype_term = mk_dep0_dep0_term subtype_opname

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_subtype

dform subtype_df1 : parens :: "prec"[prec_subtype] :: subtype{'A; 'B} =
   slot{'A} `" " subseteq space slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext subtype(A; B)
 * by subtypeFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
prim subtypeFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   subtype{'A; 'B}

(*
 * H >- subtype(A1; B1) = subtype(A2; B2) in Ui
 * by subtypeEquality
 *
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
prim subtypeEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- subtype{'A1; 'B1} = subtype{'A2; 'B2} in univ[i:l] } =
   it

prim subtypeType {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{subtype{'A; 'B}} } =
   it

prim subtypeTypeLeft 'H 'A :
   [main] sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- "type"{'B} } =
   it

prim subtypeTypeRight 'H 'B :
   [main] sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- "type"{'A} } =
   it

(*
 * H >- subtype(A; B) ext it
 * by subtype_axiomFormation
 *
 * H >- A = A in Ui
 * H; x: A; y: A; x = y in A >- x = y in B
 *)
prim subtype_axiomFormation {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [main] sequent [squash] { 'H; x: 'A >- member{'B; 'x} } -->
   sequent ['ext] { 'H >- subtype{'A; 'B} } =
   it

(*
 * H >- it = it in subtype(A; B)
 * by subtype_axiomEquality
 *
 * H >- subtype(A; B)
 *)
prim subtype_axiomEquality {| intro_resource []; eqcd_resource |} 'H :
   [main] sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- it = it in subtype{'A; 'B} } =
   it

interactive subtype_axiomMember {| intro_resource [] |} 'H :
   [main] sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- member{subtype{'A; 'B}; it} }

(*
 * H, x: subtype(A; B); J[x] >- C[x]
 * by subtypeElimination
 *
 * H, x: subtype(A; B); J[it] >- C[it]
 *)
prim subtypeElimination {| elim_resource [ThinOption thinT] |} 'H 'J :
   ('t : sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J['x] >- 'C['x] } =
   't

(*
 * H >- x = y in B
 * by subtypeElimination2 A
 *
 * H >- x = y in A
 * H >- subtype(A; B)
 *)
prim subtypeElimination2 'H 'J 'a 'y :
   [wf] sequent [squash] { 'H; x: subtype{'A; 'B}; 'J['x] >- member{'A; 'a} } -->
   ('t['y] : sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J['x]; y: member{'B; 'a} >- 'C['x] }) -->
   sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J['x] >- 'C['x] } =
   't[it]

(*
 * Squash elimination.
 *)
prim subtype_squashElimination 'H :
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- subtype{'A; 'B} } =
   it

(************************************************************************
 * SUBTYPE RESOURCE                                                     *
 ************************************************************************)

(*
 * This is what is supplied to the resource.
 *)
type sub_info_type = (term * term) list * tactic

type sub_resource_info =
   LRSubtype of sub_info_type
 | RLSubtype of sub_info_type
 | DSubtype of sub_info_type

(*
 * Subtype resource is a DAG.
 *)
type sub_data = tactic term_dtable

(*
 * The resource itself.
 *)
resource (sub_resource_info, tactic, sub_data, unit) sub_resource

(*
 * Improve the subtyping information.
 * We are provided with a (term * term) list
 * and a tactic, where the first term pair is the goal, the rest are
 * subgoals, and the supplied tactic should generate the subgoals
 * in order.
 *)
let subtype_f tac subgoals _ =
   let rec aux sg = function
      p::t ->
         let goal = concl p in
            if Opname.eq (opname_of_term goal) subtype_opname then
               match sg with
                  (_, _, tac)::sg' -> (tac p)::(aux sg' t)
                | [] -> raise (RefineError ("subtypeT", StringError "subtype mismatch"))
            else
               (idT p)::(aux sg t)
    | [] -> []
   in
      tac thenFLT aux subgoals

let improve_data base = function
   LRSubtype (goal, tac) ->
      insert_left base goal (subtype_f tac)
 | RLSubtype (goal, tac) ->
      insert_right base goal (subtype_f tac)
 | DSubtype (goal, tac) ->
      insert base goal (subtype_f tac)

(*
 * Extract a subtype tactic from the data.
 * Chain the tactics together.
 *)
let extract_data base =
   let tbl = extract base in
   let subtyper p =
      let t = concl p in
      let t1, t2 = dest_subtype t in
      let tac =
         try lookup tbl t1 t2 with
            Not_found ->
               raise (RefineError ("subtype", StringTermError ("can't infer subtype ", t)))
      in
         tac p
   in
      subtyper

(*
 * Wrap up the joiner.
 *)
let join_resource = join_tables

let extract_resource = extract_data

let improve_resource = improve_data

let close_resource rsrc modname =
   rsrc

(*
 * Resource.
 *)
let sub_resource =
   Mp_resource.create (**)
      { resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource;
        resource_improve_arg = Mp_resource.improve_arg_fail "sub_resource";
        resource_close = close_resource
      }
      (new_dtable ())

let get_resource modname =
   Mp_resource.find sub_resource modname

(*
 * Resource argument.
 *)
let subtypeT p =
   Sequent.get_tactic_arg p "subtype" p

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_subtypeT i p =
   let j, k = hyp_indices p i in
      try
         let a = get_with_arg p in
         let v, _ = Sequent.nth_hyp p i in
         let v = maybe_new_vars1 p v in
            subtypeElimination2 j k a v p
      with
         RefineError _ ->
            subtypeElimination j k p

let elim_resource = Mp_resource.improve elim_resource (subtype_term, d_hyp_subtypeT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of subtype.
 *)
let inf_subtype f decl t =
   let a, b = dest_subtype t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2 0)

let typeinf_resource = Mp_resource.improve typeinf_resource (subtype_term, inf_subtype)

(************************************************************************
 * SQUASH                                                               *
 ************************************************************************)

let squash_subtypeT p =
   subtype_squashElimination (Sequent.hyp_count_addr p) p

(************************************************************************
 * TYPEHOOD FROM SUBTYPE                                                *
 ************************************************************************)

let type_subtype_leftT a p =
   subtypeTypeLeft (Sequent.hyp_count_addr p) a p

let type_subtype_rightT b p =
   subtypeTypeRight (Sequent.hyp_count_addr p) b p

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
