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

include Itt_equal
include Itt_dprod
include Itt_struct

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type.Sequent
open Tactic_type.Tacticals

open Base_dtactic

open Itt_equal
open Itt_subtype
open Itt_dprod
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_prod%t"

(* debug_string DebugLoad "Loading itt_prod..." *)

(*
 * The independent product is defined as a dependent product.
 *)
prim_rw unfold_prod : ('A * 'B) <--> (x: 'A * 'B)

(*
 * H >- A1 * B1 = A2 * B2 in Ui
 * by independentProductEquality
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
interactive independentProductEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- 'A1 * 'B1 = 'A2 * 'B2 in univ[i:l] }

(*
 * Typehood.
 *)
interactive independentProductType {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'A1} } -->
   [wf] sequent [squash] { 'H >- "type"{'A2} } -->
   sequent ['ext] { 'H >- "type"{.'A1 * 'A2} }

(*
 * H >- Ui ext A * B
 * by independentProductFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
interactive independentProductFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H, A * B, J >- T ext t
 * by independentProductElimination
 * H, A * B, u: A, v: B, J >- T ext t
 *)
interactive independentProductElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'z 'u 'v :
   ('t['u; 'v] : sequent ['ext] { 'H; z: 'A * 'B; u: 'A; v: 'B; 'J['u, 'v] >- 'T['u, 'v] }) -->
   sequent ['ext] { 'H; z: 'A * 'B; 'J['z] >- 'T['z] }

(*
 * H >- (a1, b1) = (a2, b2) in A * B
 * by independentPairEquality
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B
 *)
interactive independentPairEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   [wf] sequent [squash] { 'H >- 'b1 = 'b2 in 'B } -->
   sequent ['ext] { 'H >- ('a1, 'b1) = ('a2, 'b2) in 'A * 'B }

(*
 * H >- A * B ext (a, b)
 * by independentPairFormation a y
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
interactive independentPairFormation {| intro_resource [] |} 'H :
   [wf] ('a : sequent ['ext] { 'H >- 'A }) -->
   [wf] ('b : sequent ['ext] { 'H >- 'B }) -->
   sequent ['ext] { 'H >- 'A * 'B }

(*
 * H >- A1 -> B1 <= A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H >- B1 <= B2
 *)
interactive independentProductSubtype {| intro_resource [] |} 'H :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 * 'B1); ('A2 * 'B2) } }

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let typeinf_resource =
   Mp_resource.improve typeinf_resource (prod_term, infer_univ_dep0_dep0 dest_prod)

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
   Mp_resource.improve
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
