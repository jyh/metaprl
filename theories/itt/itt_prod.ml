(*
 * Rules for dependent product.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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
include Itt_dprod
include Itt_struct

open Printf
open Nl_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Nl_resource

open Var
open Sequent
open Tacticals

open Itt_equal
open Itt_subtype
open Itt_dprod
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_prod%t" eflush

(* debug_string DebugLoad "Loading itt_prod..." *)

(*
 * The independent product is defined as a dependent product.
 *)
primrw unfoldProd : ('A * 'B) <--> (x: 'A * 'B)

(*
 * H >- Ui ext A * B
 * by independentProductFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
prim independentProductFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[@i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   'A * 'B

(*
 * H >- A1 * B1 = A2 * B2 in Ui
 * by independentProductEquality
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
prim independentProductEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- 'A1 * 'B1 = 'A2 * 'B2 in univ[@i:l] } =
   it

(*
 * Typehood.
 *)
prim independentProductType 'H :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H >- "type"{'A2} } -->
   sequent ['ext] { 'H >- "type"{.'A1 * 'A2} } =
   it

(*
 * H >- A * B ext (a, b)
 * by independentPairFormation a y
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
prim independentPairFormation 'H :
   ('a : sequent ['ext] { 'H >- 'A }) -->
   ('b : sequent ['ext] { 'H >- 'B }) -->
   sequent ['ext] { 'H >- 'A * 'B } =
   'a, 'b

(*
 * H, A * B, J >- T ext t
 * by independentProductElimination
 * H, A * B, u: A, v: B, J >- T ext t
 *)
prim independentProductElimination 'H 'J 'z 'u 'v :
   ('t : sequent ['ext] { 'H; z: 'A * 'B; u: 'A; v: 'B; 'J['u, 'v] >- 'T['u, 'v] }) -->
   sequent ['ext] { 'H; z: 'A * 'B; 'J['z] >- 'T['z] } =
   't

(*
 * H >- (a1, b1) = (a2, b2) in A * B
 * by independentPairEquality
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B
 *)
prim independentPairEquality 'H :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B } -->
   sequent ['ext] { 'H >- ('a1, 'b1) = ('a2, 'b2) in 'A * 'B } =
   it

(*
 * H >- A1 -> B1 <= A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H >- B1 <= B2
 *)
prim independentProductSubtype 'H :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 * 'B1); ('A2 * 'B2) } } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_prod p =
   let count = hyp_count_addr p in
      independentPairFormation count p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_prod i p =
   let z, _ = Sequent.nth_hyp p i in
   let i', j = hyp_indices p i in
   let u, v = maybe_new_vars2 p "u" "v" in
   let tac = independentProductElimination i' j z u v in
      if get_thinning_arg p then
         (tac thenT thinT i) p
      else
         tac p

(*
 * Join them.
 *)
let d_prodT i =
   if i = 0 then
      d_concl_prod
   else
      d_hyp_prod i

let d_resource = d_resource.resource_improve d_resource (prod_term, d_prodT)

(*
 * Typehood.
 *)
let d_prod_typeT i p =
   if i = 0 then
      independentProductType (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_prod_typeT", StringError "no elimination form"))

let prod_type_term = << "type"{.'A1 * 'A2} >>

let d_resource = d_resource.resource_improve d_resource (prod_type_term, d_prod_typeT)

(*
 * EQCD.
 *)
let eqcd_prodT p =
   let count = hyp_count_addr p in
      (independentProductEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (prod_term, eqcd_prodT)

let prod_equal_term = << ('a1 * 'a2) = ('b1 * 'b2) in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (prod_equal_term, d_wrap_eqcd eqcd_prodT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of rfun.
 *)
let inf_prod f decl t =
   let a, b = dest_prod t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (prod_term, inf_prod)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two product types.
 *)
let prod_subtypeT p =
   (independentProductSubtype (hyp_count_addr p)
    thenT addHiddenLabelT "subtype") p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (DSubtype ([<< 'A1 * 'B1 >>, << 'A2 * 'B2 >>;
               << 'A1 >>, << 'A2 >>;
               << 'B1 >>, << 'B2 >>],
              prod_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
