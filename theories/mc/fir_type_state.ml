(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Type judgements for FIR state operations.
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
 * Author: Brian Emre Aydemir
 * Email:  emre@its.caltech.edu
 *)

include Base_theory
include Itt_theory
include Fir_state
include Fir_type

open Base_dtactic

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Block type. *)
declare ty_block

(* Triple type. *)
declare ty_triple{ 'A; 'B; 'C }

(* State type. *)
declare ty_state

(* Reference type. *)
declare ty_ref

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Block type. *)
dform ty_block_df : except_mode[src] :: ty_block =
   `"Ty_block"

(* Triple type. *)
dform ty_triple_df : except_mode[src] :: ty_triple{ 'A; 'B; 'C } =
   `"TyTriple(" slot{'A} `", " slot{'B} `", " slot{'C} `")"

(* State type. *)
dform ty_state_df : except_mode[src] :: ty_state =
   `"Ty_state"

(* Reference type. *)
dform ty_ref_df : except_mode[src] :: ty_ref =
   `"Ty_ref"

(*************************************************************************
 * Rules.
 *************************************************************************)

(*
 * Block equality.
 *)

prim ty_block_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- ty_block = ty_block in fir_univ }
   = it

prim ty_block_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'tag1 = 'tag2 in int } -->
   [wf] sequent ['ext] { 'H >- 'args1 = 'args2 in array{fir_value} } -->
   sequent ['ext]
      { 'H >- block{'tag1; 'args1} = block{'tag2; 'args2} in ty_block }
   = it

prim nth_block_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- 'b1 = 'b2 in ty_block } -->
   sequent ['ext] { 'H >- 'i1 = 'i2 in int } -->
   sequent ['ext] { 'H >-
      nth_block{ 'b1; 'i1 } = nth_block{ 'b2; 'i2 } in 'T }
   = it

(*
 * Triple equality.
 *)

prim ty_triple_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'A1 = 'A2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'B1 = 'B2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'C1 = 'C2 in fir_univ } -->
   sequent ['ext] { 'H >-
      ty_triple{'A1; 'B1; 'C1} = ty_triple{'A2; 'B2; 'C2} in fir_univ }
   = it

prim ty_triple_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'a1 = 'a2 in 'A } -->
   [wf] sequent ['ext] { 'H >- 'b1 = 'b2 in 'B } -->
   [wf] sequent ['ext] { 'H >- 'c1 = 'c2 in 'C } -->
   sequent ['ext] { 'H >-
      triple{'a1; 'b1; 'c1} = triple{'a2; 'b2; 'c2} in ty_triple{'A; 'B; 'C} }
   = it

(*
 * State equality.
 *)

prim ty_state_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- ty_state = ty_state in fir_univ }
   = it

prim ty_state_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'n1 = 'n2 in int } -->
(* I could make the following assertion stronger by requiring
 * that 'n1 equal the length of 'a1. *)
   [wf] sequent ['ext] { 'H >- "assert"{ le_bool{ 0; 'n1 } } } -->
   [wf] sequent ['ext] { 'H >- 'a1 = 'a2 in array{ ty_block } } -->
   sequent ['ext] { 'H >- pair{ 'n1; 'a1 } = pair{ 'n2; 'a2 } in ty_state }
   = it

interactive empty_ty_state_member_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- empty = empty in ty_state }

(*
 * Match equality.
 *)

interactive smatch_equality {| intro [] |} 'H :
   [wf] sequent ['ext]
      { 'H >- pair{'a1; 'b2} = pair{'a2; 'b2} in ty_state } -->
   [wf] sequent ['ext] { 'H >- 'c1 = 'c2 in fir_value } -->
   [main] sequent ['ext] { 'H >-
      'e1[ pair{'a1; 'b1}; 'c1 ] = 'e2[ pair{'a2; 'b2}; 'c2 ] in 'T } -->
   sequent ['ext] { 'H >-
      smatch{ triple{'a1; 'b1; 'c1}; x1, y1. 'e1['x1; 'y1] } =
      smatch{ triple{'a2; 'b2; 'c2}; x2, y2. 'e2['x2; 'y2] } in 'T }

(*
 * Reference equality.
 *)

prim ty_ref_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- ty_ref = ty_ref in fir_univ }
   = it

prim ty_ref_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'i = 'j in int } -->
   sequent ['ext] { 'H >- ref{ 'i } = ref{ 'j } in ty_ref }
   = it

(*
 * State operations equality.
 *)

prim alloc_equality {| intro [] |} 'H :
   [wf] sequent ['ext]
      { 'H >- pair{'n1; 's1} = pair{'n2; 's2} in ty_state } -->
   [wf] sequent ['ext] { 'H >- 't1 = 't2 in int } -->
   [wf] sequent ['ext] { 'H >- 'i1 = 'i2 in array{fir_value} } -->
   sequent ['ext] { 'H >-
      alloc{ pair{'n1; 's1}; 't1; 'i1 } =
      alloc{ pair{'n2; 's2}; 't2; 'i2 }
      in ty_triple{ int; array{ty_block}; ty_ref } }
   = it

prim store_equality {| intro [] |} 'H :
   [wf] sequent ['ext]
      { 'H >- pair{'n1; 's1} = pair{'n3; 's2} in ty_state } -->
   [wf] sequent ['ext] { 'H >- ref{'n2} = ref{'n4} in ty_ref } -->
   [wf] sequent ['ext] { 'H >- 'i1 = 'i2 in int } -->
   [wf] sequent ['ext] { 'H >- 'list1 = 'list2 in array{fir_value} } -->
   sequent ['ext] { 'H >-
      store{ pair{'n1; 's1}; ref{'n2}; 'i1; 'list1 } =
      store{ pair{'n3; 's2}; ref{'n4}; 'i2; 'list2 }
      in ty_triple{ int; array{ty_block}; unit } }
   = it

prim fetch_equality {| intro [] |} 'H :
   [wf] sequent ['ext]
      { 'H >- pair{'n1; 's1} = pair{'n3; 's2} in ty_state } -->
   [wf] sequent ['ext] { 'H >- ref{'n2} = ref{'n4} in ty_ref } -->
   [wf] sequent ['ext] { 'H >- 'i1 = 'i2 in int } -->
   sequent ['ext] { 'H >-
      fetch{ pair{'n1; 's1}; ref{'n2}; 'i1 } =
      fetch{ pair{'n3; 's2}; ref{'n4}; 'i2 }
      in ty_triple{ int; array{ty_block}; 'T } }
   = it
