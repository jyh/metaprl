(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define a type system for FIR types.
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
include Fir_ty

open Base_dtactic

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Universe of FIR types. *)
declare fir_univ

(* Product type. *)
declare prod{ 'A; 'B }

(* Disjoint union type. *)
declare dunion{ 'A; 'B }
declare inl{ 'x }
declare inr{ 'x }

(* Array type. *)
declare array{ 'A }

(* Function type from 'A to 'B *)
declare ty_fun{ 'A; 'B }

(* Universally quantified type. *)
declare ty_all{ x. 'ty['x] }

(* Existentially quantified type. *)
declare ty_exists{ x. 'ty['x] }

(* Recursive type *)
declare "rec"{ x. 'ty['x] }

(* Integer set type. *)
declare ty_interval
declare ty_int_set

(* FIR value type. *)
declare fir_value

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Universe of FIR types. *)
dform fir_univ_df : except_mode[src] :: fir_univ =
   Nuprl_font!mathbbU `"[fir]"

(* Product type. *)
dform prod_df : except_mode[src] :: prod{ 'A; 'B } =
   `"(" slot{'A} `" " Nuprl_font!times `" " slot{'B} `")"

(* Disjoint union type. *)
dform dunion_df : except_mode[src] :: dunion{ 'A; 'B } =
   `"(" slot{'A} `" " Nuprl_font!cup `" " slot{'B} `")"
dform inl_df : except_mode[src] :: inl{ 'x } =
   `"inl(" slot{'x} `")"
dform inr_df : except_mode[src] :: inr{ 'x } =
   `"inr(" slot{'x} `")"

(* Array type. *)
dform array_df : except_mode[src] :: array{ 'A } =
   slot{'A} `" Array"

(* Function type from 'A to 'B. *)
dform ty_fun_df : except_mode[src] :: ty_fun{ 'A; 'B } =
   slot{'A} `" " Nuprl_font!rightarrow `" " slot{'B}

(* Universally quantified type. *)
dform all_df : except_mode[src] :: ty_all{ x. 'ty } =
   Nuprl_font!forall slot{'x} `"." slot{'ty}

(* Existentially quantified type. *)
dform exist_df : except_mode[src] :: ty_exists{ x. 'ty } =
   Nuprl_font!exists slot{'x} `"." slot{'ty}

(* Recursive type. *)
dform rec_df : except_mode[src] :: "rec"{ x. 'ty } =
   Nuprl_font!mu slot{'x} `"." slot{'ty}

(* Integer set type. *)
dform ty_interval_df : except_mode[src] :: ty_interval =
   `"Ty_interval"
dform ty_int_set_df : except_mode[src] :: ty_int_set =
   `"Ty_int_set"

(* FIR value type. *)
dform fir_value_df : except_mode[src] :: fir_value =
   `"Fir_value"

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* We treat tyInt's as regular ITT ints. *)
prim_rw reduce_tyInt : tyInt <--> int

(* Function type. *)
prim_rw reduce_tyFun1 :
   tyFun{ nil; 'ty } <--> 'ty
prim_rw reduce_tyFun2 :
   tyFun{ cons{'h; 't}; 'ty } <--> ty_fun{ 'h; tyFun{'t; 'ty} }

(*
 * Represent tuples as products.  The empty tuple, i.e. the tuple
 * with a ty_list of nil makes no sense, so there's no rewrite for it.
 *)
prim_rw reduce_tyTuple1 : tyTuple{ cons{'h; nil} } <--> 'h
prim_rw reduce_tyTuple2 : tyTuple{ cons{'h; 't} } <--> ('h * tyTuple{'t})

(* Arrays are like lists. *)
prim_rw reduce_tyArray : tyArray{'ty} <--> array{'ty}

(* Existential and universal quantification. *)
prim_rw reduce_tyExists1 :
   tyExists{ cons{'h; nil}; 'ty } <--> ty_exists{ h. 'ty }
prim_rw reduce_tyExists2 :
   tyExists{ cons{'h; 't}; 'ty } <--> ty_exists{ h. tyExists{'t; 'ty} }
prim_rw reduce_tyAll1 :
   tyAll{ cons{'h; nil}; 'ty } <--> ty_all{ h. 'ty }
prim_rw reduce_tyAll2 :
   tyAll{ cons{'h; 't}; 'ty } <--> ty_all{ h. tyAll{ 't; 'ty } }

(* Automation for rewrites. *)
let resource reduce += [
   << tyInt >>, reduce_tyInt;
   << tyFun{ nil; 'ty } >>, reduce_tyFun1;
   << tyFun{ cons{'h; 't}; 'ty } >>, reduce_tyFun2;
   << tyTuple{ cons{'h; nil} } >>, reduce_tyTuple1;
   << tyTuple{ cons{'h; 't} } >>, reduce_tyTuple2;
   << tyArray{'ty} >>, reduce_tyArray;
   << tyExists{ cons{'h; nil}; 'ty } >>, reduce_tyExists1;
   << tyExists{ cons{'h; 't}; 'ty } >>, reduce_tyExists2;
   << tyAll{ cons{'h; nil}; 'ty } >>, reduce_tyAll1;
   << tyAll{ cons{'h; 't}; 'ty } >>, reduce_tyAll2;
]

(*************************************************************************
 * Rules.
 *************************************************************************)

(*
 * Integer type.
 * This is probably the only type where the ITT notion of a type
 *    being true does not effect us here.
 *)

prim int_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- int = int in fir_univ }
   = it

interactive tyInt_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- tyInt = tyInt in fir_univ }

interactive number_tyInt_membership {| intro [] |} 'H :
   sequent ['ext] { 'H >- number[i:n] = number[i:n] in tyInt }

interactive int_tyInt_folding_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'i = 'j in tyInt } -->
   sequent ['ext] { 'H >- 'i = 'j in int }

interactive minus_int_tyInt_membership {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'a = 'b in tyInt } -->
   sequent ['ext] { 'H >- minus{'a} = minus{'b} in tyInt }

(*
 * Enumeration type.
 *)

prim tyEnum_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'a = 'b in int } -->
   sequent ['ext] { 'H >- tyEnum{'a} = tyEnum{'b} in fir_univ }
   = it

prim number_tyEnum_membership {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'a = 'b in int } -->
   [main] sequent ['ext] { 'H >- "assert"{ lt_bool{'a; 'c} } } -->
   [main] sequent ['ext] { 'H >- "assert"{ le_bool{0; 'a} } } -->
   sequent ['ext]{ 'H >- 'a = 'b in tyEnum{'c} }
   = it

interactive atomEnum_tyEnum_membership {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'a = 'b in int } -->
   [main] sequent ['ext] { 'H >- "assert"{ lt_bool{'a; 'c} } } -->
   [main] sequent ['ext] { 'H >- "assert"{ le_bool{0; 'a} } } -->
   sequent ['ext]{ 'H >- 'a = 'b in tyEnum{'c} }

(*
 * Product type.
 * The ITT rules should be sufficient here. If needed,
 *    pair membership/equality may need to be defined here since that
 *    seems to depend on the Itt_equal!"type" judgement.
 *)

prim prod_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'A1 = 'A2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'B1 = 'B2 in fir_univ } -->
   sequent ['ext] { 'H >- ('A1 * 'B1) = ('A2 * 'B2) in fir_univ }
   = it

(*
 * Disjoint union type.
 *)

prim dunion_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'A1 = 'A2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'B1 = 'B2 in fir_univ } -->
   sequent ['ext] { 'H >- dunion{'A1; 'B1} = dunion{'A2; 'B2} in fir_univ }
   = it

prim dunion_inl_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'x1 = 'x2 in 'A } -->
   [wf] sequent ['ext] { 'H >- 'B = 'B in fir_univ } -->
   sequent ['ext] { 'H >- inl{'x1} = inl{'x2} in dunion{'A; 'B} }
   = it

prim dunion_inr_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'A = 'A in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'x1 = 'x2 in 'B } -->
   sequent ['ext] { 'H >- inr{'x1} = inr{'x2} in dunion{'A; 'B} }
   = it

prim dunion_elim {| elim [] |} 'H 'J 'v1 'v2 :
   [main] sequent ['ext] { 'H; v1: 'A; 'J[ inl{'v1} ] >- 'C[ inl{'v1} ] } -->
   [main] sequent ['ext] { 'H; v2: 'B; 'J[ inr{'v2} ] >- 'C[ inr{'v2} ] } -->
   sequent ['ext] { 'H; v: dunion{'A; 'B}; 'J['v] >- 'C['v] }
   = it

(*
 * Array type.
 *)

prim array_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'A = 'B in fir_univ } -->
   sequent ['ext] { 'H >- array{'A} = array{'B} in fir_univ }
   = it

interactive tyArray_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'A = 'B in fir_univ } -->
   sequent ['ext] { 'H >- tyArray{'A} = tyArray{'B} in fir_univ }

prim array_nil_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- array{'A} = array{'A} in fir_univ } -->
   sequent ['ext] { 'H >- nil = nil in array{'A} }
   = it

prim array_cons_member_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'h1 = 'h2 in 'T } -->
   [wf] sequent ['ext] { 'H >- 't1 = 't2 in array{'T} } -->
   sequent ['ext] { 'H >- cons{'h1; 't1} = cons{'h2; 't2} in array{'T} }
   = it

prim array_elim {| elim [] |} 'H 'J 'u 'a 'b 'c :
   [main] sequent ['ext] { 'H; u: array{'A}; 'J['u] >- 'C[ nil ] } -->
   [main] sequent ['ext]
      { 'H; v: array{'A}; 'J['v]; a: 'A; b: array{'A}; c: 'C['a] >-
        'C[ cons{'a; 'b} ] } -->
   sequent ['ext] { 'H; v: array{'A}; 'J['v] >- 'C['v] }
   = it

(*
 * Function type.
 * We use an intentional equality.
 *)

prim ty_fun_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'A1 = 'A2 in fir_univ } -->
   [wf] sequent ['ext] { 'H >- 'B1 = 'B2 in fir_univ } -->
   sequent ['ext] { 'H >- ty_fun{'A1; 'B1} = ty_fun{'A2; 'B2} in fir_univ }
   = it

prim lambda_member_equality {| intro [] |} 'H 'x :
   [wf] sequent ['ext] { 'H; x: 'A >- 'f1['x] = 'f2['x] in 'B } -->
   sequent ['ext] { 'H >-
      lambda{ x1. 'f1['x1] } = lambda{ x2. 'f2['x2] } in ty_fun{'A; 'B} }
   = it

(* Is this completely correct? *)
prim apply_equality {| intro [] |} 'H 'A :
   [wf] sequent ['ext] { 'H >- 'x1 = 'x2 in 'A } -->
   [wf] sequent ['ext] { 'H >- 'f1 = 'f2 in ty_fun{'A; 'B} } -->
   sequent ['ext] { 'H >- apply{ 'f1; 'x1 } = apply{ 'f2; 'x2 } in 'B }
   = it

(*
 * Universally quantified type.
 *)

prim all_equality {| intro [] |} 'H 'a :
   [wf] sequent ['ext] { 'H; a: 'T >- 'ty1['a] = 'ty2['a] in 'T } -->
   sequent ['ext] { 'H >-
      ty_all{ x1. 'ty1['x1] } =
      ty_all{ x2. 'ty2['x2] } in 'T }
   = it

(*
 * Existentially quantified type.
 *)

prim exist_equality {| intro [] |} 'H 'a :
   [wf] sequent ['ext] { 'H; a: 'T >- 'ty1['a] = 'ty2['a] in 'T } -->
   sequent ['ext] { 'H >-
      ty_exists{ x1. 'ty1['x1] } =
      ty_exists{ x2. 'ty2['x2] } in 'T }
   = it

(*
 * Recursive type.
 *)

prim rec_equality {| intro[] |} 'H 'x :
   [wf] sequent ['ext]
      { 'H; x: fir_univ >- 'ty1['x] = 'ty2['x] in fir_univ } -->
   sequent ['ext]
      { 'H >- "rec"{x1. 'ty1['x1]} = "rec"{x2. 'ty2['x2]} in fir_univ }
   = it

prim rec_unfold_intro {| intro [] |} 'H :
   [main] sequent ['ext]
      { 'H >- 'ty1[ "rec"{x. 'ty1['x]} ] = 'ty2 in fir_univ } -->
   sequent ['ext] { 'H >- "rec"{ x. 'ty1['x] } = 'ty2 in fir_univ }
   = it

prim rec_unfold_elim {| elim [] |} 'H 'J :
   [main] sequent ['ext]
      { 'H; y: 'ty[ "rec"{ x. 'ty['x] } ]; 'J['y] >- 'C['y] } -->
   sequent ['ext] { 'H; y: "rec"{ x. 'ty['x] }; 'J['y] >- 'C['y] }
   = it

(*
 * Integer set type.
 *)

prim ty_interval_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- ty_interval = ty_interval in fir_univ }
   = it

prim interval_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'a1 = 'a2 in int } -->
   [wf] sequent ['ext] { 'H >- 'b1 = 'b2 in int } -->
   sequent ['ext]
      { 'H >- interval{'a1; 'b1} = interval{'a2; 'b2} in ty_interval }
   = it

prim ty_int_set_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- ty_int_set = ty_int_set in fir_univ }
   = it

prim int_set_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'A = 'B in array{ ty_interval } } -->
   sequent ['ext] { 'H >- int_set{'A} = int_set{'B} in ty_int_set }
   = it

interactive int_set_short_equality {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'a1 = 'a2 in int } -->
   [wf] sequent ['ext] { 'H >- 'b1 = 'b2 in int } -->
   sequent ['ext] { 'H >- int_set{'a1; 'b1} = int_set{'a2; 'b2} in ty_int_set }

interactive member_nil_in_bool {| intro [] |} 'H :
   sequent ['ext] { 'H >-
      member{ 'n1; int_set{nil} } =
      member{ 'n2; int_set{nil} } in bool }

interactive true_set_member_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- true_set = true_set in ty_int_set }

interactive false_set_member_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- false_set = false_set in ty_int_set }

(*
 * FIR value type.
 * Essentially, any values that are in any of the above types,
 *    are also in fir_value.
 *)

prim fir_value_equality {| intro [] |} 'H :
   sequent ['ext] { 'H >- fir_value = fir_value in fir_univ }
   = it

prim number_member_fir_value {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- number[i:n] = number[j:n] in int } -->
   sequent ['ext] { 'H >- number[i:n] = number[j:n] in fir_value }
   = it

prim nil_member_fir_value {| intro [] |} 'H :
   sequent ['ext] { 'H >- nil = nil in fir_value }
   = it

prim cons_member_fir_value {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'h1 = 'h2 in fir_value } -->
   [wf] sequent ['ext] { 'H >- 't1 = 't2 in fir_value } -->
   sequent ['ext] { 'H >- cons{'h1; 't1} = cons{'h2; 't2} in fir_value }
   = it
