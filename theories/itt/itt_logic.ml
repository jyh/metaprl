(*
 * Regular logic connectives.
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
include Itt_rfun
include Itt_dfun
include Itt_fun
include Itt_dprod
include Itt_prod
include Itt_union
include Itt_void
include Itt_unit
include Itt_struct

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Mptop
open Var

open Base_auto_tactic
open Base_dtactic

open Itt_squash
open Itt_void
open Itt_equal
open Itt_rfun
open Itt_dprod
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_logic%t"

let debug_auto =
   create_debug (**)
      { debug_name = "auto";
        debug_description = "Display auto tactic operations";
        debug_value = false
      }

(************************************************************************
 * REWRITES								*
 ************************************************************************)

declare "prop"[i:l]

declare "true"
declare "false"
declare "not"{'a}
declare "iff"{'a; 'b}
declare "implies"{'a; 'b}
declare "and"{'a; 'b}
declare "or"{'a; 'b}
declare "cand"{'a; 'b}
declare "cor"{'a; 'b}
declare "all"{'A; x. 'B['x]}
declare "exists"{'A; x. 'B['x]}

prim_rw unfold_prop : "prop"[i:l] <--> "univ"[i:l]

prim_rw unfold_true : "true" <--> unit
prim_rw unfold_false : "false" <--> void
prim_rw unfold_not : "not"{'a} <--> ('a -> void)
prim_rw unfold_implies : ('a => 'b) <--> ('a -> 'b)
prim_rw unfold_iff : "iff"{'a; 'b} <--> (('a -> 'b) & ('b -> 'a))
prim_rw unfold_and : ('a & 'b) <--> ('a * 'b)
prim_rw unfold_or : ('a or 'b) <--> ('a + 'b)
prim_rw unfold_cand : "cand"{'a; 'b} <--> ('a & 'b)
prim_rw unfold_cor : "cor"{'a; 'b} <--> "or"{'a; ."cand"{."not"{'a}; 'b}}
prim_rw unfold_all : (all x: 'A. 'B['x]) <--> (x:'A -> 'B['x])
prim_rw unfold_exists : (exst x: 'A. 'B['x]) <--> (x:'A * 'B['x])

let fold_true    = makeFoldC << "true" >> unfold_true
let fold_false   = makeFoldC << "false" >> unfold_false
let fold_not     = makeFoldC << not{'a} >> unfold_not
let fold_implies = makeFoldC << 'a => 'b >> unfold_implies
let fold_iff     = makeFoldC << "iff"{'a; 'b} >> unfold_iff
let fold_and     = makeFoldC << 'a & 'b >> unfold_and
let fold_or      = makeFoldC << 'a or 'b >> unfold_or
let fold_cand    = makeFoldC << "cand"{'a; 'b} >> unfold_cand
let fold_cor     = makeFoldC << "cor"{'a; 'b} >> unfold_cor
let fold_all     = makeFoldC << all x: 'A. 'B['x] >> unfold_all
let fold_exists  = makeFoldC << exst x: 'A. 'B['x] >> unfold_exists

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * True and false.
 *)
interactive true_univ {| intro_resource []; eqcd_resource |} 'H :
   sequent ['ext] { 'H >- "true" = "true" in univ[i:l] }

interactive true_member {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- member{univ[i:l]; ."true"} }

interactive true_type {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "type"{."true"} }

interactive true_intro {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "true" }

interactive false_univ {| intro_resource []; eqcd_resource |} 'H :
   sequent ['ext] { 'H >- "false" = "false" in univ[i:l] }

interactive false_member {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "member"{univ[i:l]; ."false"} }

interactive false_type {| intro_resource [] |} 'H :
   sequent ['ext] { 'H >- "type"{."false"} }

interactive false_elim {| elim_resource [ThinOption thinT] |} 'H 'J :
   sequent ['ext] { 'H; x: "false"; 'J['x] >- 'C['x] }

interactive false_squash 'H :
   sequent [squash] { 'H >- "false" } -->
   sequent ['ext] { 'H >- "false" }

(*
 * Negation.
 *)
interactive not_univ {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 't1 = 't2 in univ[i:l] } -->
   sequent ['ext] { 'H >- "not"{'t1} = "not"{'t2} in univ[i:l] }

interactive not_member {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 't} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; ."not"{'t}} }

interactive not_type {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'t} } -->
   sequent ['ext] { 'H >- "type"{."not"{'t}} }

interactive not_intro {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'t} } -->
   [main] sequent ['ext] { 'H; x: 't >- "false" } -->
   sequent ['ext] { 'H >- "not"{'t} }

interactive not_elim {| elim_resource [] |} 'H 'J :
   [assertion] sequent ['ext] { 'H; x: "not"{'t}; 'J['x] >- 't } -->
   sequent ['ext] { 'H; x: "not"{'t}; 'J['x] >- 'C }

(*
 * Conjunction.
 *)
interactive and_univ {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in univ[i:l] } -->
   sequent ['ext] { 'H >- "and"{'a1; 'a2} = "and"{'b1; 'b2} in univ[i:l] }

interactive and_member {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'a1} } -->
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'a2} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; ."and"{'a1; 'a2}} }

interactive and_type {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'a1} } -->
   [wf] sequent [squash] { 'H >- "type"{'a2} } -->
   sequent ['ext] { 'H >- "type"{."and"{'a1; 'a2}} }

interactive and_intro {| intro_resource [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'a1 } -->
   [wf] sequent ['ext] { 'H >- 'a2 } -->
   sequent ['ext] { 'H >- "and"{'a1; 'a2} }

interactive and_elim {| elim_resource [] |} 'H 'J 'y 'z :
   [main] sequent ['ext] { 'H; y: 'a1; z: 'a2; 'J['y, 'z] >- 'C['y, 'z] } -->
   sequent ['ext] { 'H; x: "and"{'a1; 'a2}; 'J['x] >- 'C['x] }

(*
 * Disjunction.
 *)
interactive or_univ {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in univ[i:l] } -->
   sequent ['ext] { 'H >- "or"{'a1; 'a2} = "or"{'b1; 'b2} in univ[i:l] }

interactive or_member {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'a1} } -->
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'a2} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; ."or"{'a1; 'a2}} }

interactive or_type {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'a1} } -->
   [wf] sequent [squash] { 'H >- "type"{'a2} } -->
   sequent ['ext] { 'H >- "type"{."or"{'a1; 'a2}} }

interactive or_intro_left {| intro_resource [SelectOption 1] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{.'a2} } -->
   [main] sequent ['ext] { 'H >- 'a1 } -->
   sequent ['ext] { 'H >- "or"{'a1; 'a2} }

interactive or_intro_right {| intro_resource [SelectOption 2] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{.'a1} } -->
   [main] sequent ['ext] { 'H >- 'a2 } -->
   sequent ['ext] { 'H >- "or"{'a1; 'a2} }

interactive or_elim {| elim_resource [] |} 'H 'J 'y :
   [main] sequent ['ext] { 'H; y: 'a1; 'J[inl{'y}] >- 'C[inl{'y}] } -->
   [main] sequent ['ext] { 'H; y: 'a2; 'J[inr{'y}] >- 'C[inr{'y}] } -->
   sequent ['ext] { 'H; x: "or"{'a1; 'a2}; 'J['x] >- 'C['x] }

(*
 * Implication.
 *)
interactive implies_univ {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in univ[i:l] } -->
   sequent ['ext] { 'H >- "implies"{'a1; 'a2} = "implies"{'b1; 'b2} in univ[i:l] }

interactive implies_member {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'a1} } -->
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'a2} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; ."implies"{'a1; 'a2}} }

interactive implies_type {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'a1} } -->
   [wf] sequent [squash] { 'H >- "type"{'a2} } -->
   sequent ['ext] { 'H >- "type"{."implies"{'a1; 'a2}} }

interactive implies_intro {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'a1} } -->
   [main] sequent ['ext] { 'H; x: 'a1 >- 'a2 } -->
   sequent ['ext] { 'H >- "implies"{'a1; 'a2} }

interactive implies_elim {| elim_resource [ThinOption thinT] |} 'H 'J 'y :
   [assertion] sequent ['ext] { 'H; x: "implies"{'a1; 'a2}; 'J['x] >- 'a1 } -->
   [main] sequent ['ext] { 'H; x: "implies"{'a1; 'a2}; 'J['x]; y: 'a2 >- 'C['x] } -->
   sequent ['ext] { 'H; x: "implies"{'a1; 'a2}; 'J['x] >- 'C['x] }

(*
 * Bi-implication.
 *)
interactive iff_univ {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'a2 = 'b2 in univ[i:l] } -->
   sequent ['ext] { 'H >- "iff"{'a1; 'a2} = "iff"{'b1; 'b2} in univ[i:l] }

interactive iff_member {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'a1} } -->
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'a2} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; ."iff"{'a1; 'a2}} }

interactive iff_type {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'a1} } -->
   [wf] sequent [squash] { 'H >- "type"{'a2} } -->
   sequent ['ext] { 'H >- "type"{."iff"{'a1; 'a2}} }

interactive iff_intro {| intro_resource [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'a1 => 'a2 } -->
   [wf] sequent ['ext] { 'H >- 'a2 => 'a1 } -->
   sequent ['ext] { 'H >- "iff"{'a1; 'a2} }

interactive iff_elim {| elim_resource [] |} 'H 'J 'y 'z :
   sequent ['ext] { 'H; y: "implies"{'a1; 'a2}; z: "implies"{'a2; 'a1}; 'J['y, 'z] >- 'C['y, 'z] } -->
   sequent ['ext] { 'H; x: "iff"{'a1; 'a2}; 'J['x] >- 'C['x] }

(*
 * Conjunction.
 *)
interactive cand_univ {| intro_resource []; eqcd_resource |} 'H 'x :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'a1 >- 'a2 = 'b2 in univ[i:l] } -->
   sequent ['ext] { 'H >- "cand"{'a1; 'a2} = "cand"{'b1; 'b2} in univ[i:l] }

interactive cand_member {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'a1} } -->
   [wf] sequent [squash] { 'H; x: 'a1 >- member{univ[i:l]; 'a2} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; ."cand"{'a1; 'a2}} }

interactive cand_type {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'a1} } -->
   [wf] sequent [squash] { 'H; x: 'a1 >- "type"{'a2} } -->
   sequent ['ext] { 'H >- "type"{."cand"{'a1; 'a2}} }

interactive cand_intro {| intro_resource [] |} 'H 'x :
   [main] sequent ['ext] { 'H >- 'a1 } -->
   [main] sequent ['ext] { 'H; x: 'a1 >- 'a2 } -->
   sequent ['ext] { 'H >- "cand"{'a1; 'a2} }

interactive cand_elim {| elim_resource [] |} 'H 'J 'y 'z :
   [main] sequent ['ext] { 'H; y: 'a1; z: 'a2; 'J['y, 'z] >- 'C['y, 'z] } -->
   sequent ['ext] { 'H; x: "cand"{'a1; 'a2}; 'J['x] >- 'C['x] }

(*
 * Disjunction.
 *)
interactive cor_univ {| intro_resource []; eqcd_resource |} 'H 'x :
   [wf] sequent [squash] { 'H >- 'a1 = 'b1 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: "not"{'a1} >- 'a2 = 'b2 in univ[i:l] } -->
   sequent ['ext] { 'H >- "cor"{'a1; 'a2} = "cor"{'b1; 'b2} in univ[i:l] }

interactive cor_member {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 'a1} } -->
   [wf] sequent [squash] { 'H; x: "not"{'a1} >- member{univ[i:l]; 'a2} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; ."cor"{'a1; 'a2}} }

interactive cor_type {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'a1} } -->
   [wf] sequent [squash] { 'H; x: "not"{'a1} >- "type"{'a2} } -->
   sequent ['ext] { 'H >- "type"{."cor"{'a1; 'a2}} }

interactive cor_intro_left {| intro_resource [SelectOption 1] |} 'H 'x :
   [wf] sequent [squash] { 'H; x: "not"{'a1} >- "type"{.'a2} } -->
   [main] sequent ['ext] { 'H >- 'a1 } -->
   sequent ['ext] { 'H >- "cor"{'a1; 'a2} }

interactive cor_intro_right {| intro_resource [SelectOption 2] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{.'a1} } -->
   [main] sequent ['ext] { 'H >- "not"{'a1} } -->
   [main] sequent ['ext] { 'H; x: "not"{'a1} >- 'a2 } -->
   sequent ['ext] { 'H >- "cor"{'a1; 'a2} }

interactive cor_elim {| elim_resource [] |} 'H 'J 'u 'v :
   [main] sequent ['ext] { 'H; u: 'a1; 'J[inl{'u}] >- 'C[inl{'u}] } -->
   [main] sequent ['ext] { 'H; u: "not"{'a1}; v: 'a2; 'J[inr{'u, 'v}] >- 'C[inr{'u, 'v}] } -->
   sequent ['ext] { 'H; x: "cor"{'a1; 'a2}; 'J['x] >- 'C['x] }

(*
 * All elimination performs a thinning
 *)
interactive all_univ {| intro_resource []; eqcd_resource |} 'H 'x :
   [wf] sequent [squash] { 'H >- 't1 = 't2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x : 't1 >- 'b1['x] = 'b2['x] in univ[i:l] } -->
   sequent ['ext] { 'H >- "all"{'t1; x1. 'b1['x1]} = "all"{'t2; x2. 'b2['x2]} in univ[i:l] }

interactive all_member {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 't} } -->
   [wf] sequent [squash] { 'H; x: 't >- member{univ[i:l]; 'b['x]} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; ."all"{'t; v. 'b['v]}} }

interactive all_type {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'t} } -->
   [wf] sequent [squash] { 'H; x: 't >- "type"{'b['x]} } -->
   sequent ['ext] { 'H >- "type"{."all"{'t; v. 'b['v]}} }

interactive all_intro {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'t} } -->
   [main] sequent ['ext] { 'H; x: 't >- 'b['x] } -->
   sequent ['ext] { 'H >- "all"{'t; v. 'b['v]} }

interactive all_elim {| elim_resource [ThinOption thinT] |} 'H 'J 'w 'z :
   [wf] sequent [squash] { 'H; x: all a: 'A. 'B['a]; 'J['x] >- member{'A; 'z} } -->
   [main] sequent ['ext] { 'H; x: all a: 'A. 'B['a]; 'J['x]; w: 'B['z] >- 'C['x] } -->
   sequent ['ext] { 'H; x: all a: 'A. 'B['a]; 'J['x] >- 'C['x] }

(*
 * Existential.
 *)
interactive exists_univ {| intro_resource []; eqcd_resource |} 'H 'x :
   [wf] sequent [squash] { 'H >- 't1 = 't2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x : 't1 >- 'b1['x] = 'b2['x] in univ[i:l] } -->
   sequent ['ext] { 'H >- "exists"{'t1; x1. 'b1['x1]} = "exists"{'t2; x2. 'b2['x2]} in univ[i:l] }

interactive exists_member {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- member{univ[i:l]; 't} } -->
   [wf] sequent [squash] { 'H; x: 't >- member{univ[i:l]; 'b['x]} } -->
   sequent ['ext] { 'H >- member{univ[i:l]; ."exists"{'t; v. 'b['v]}} }

interactive exists_type {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- "type"{'t} } -->
   [wf] sequent [squash] { 'H; x: 't >- "type"{'b['x]} } -->
   sequent ['ext] { 'H >- "type"{."exists"{'t; v. 'b['v]}} }

interactive exists_intro {| intro_resource [] |} 'H 'z 'x :
   [wf] sequent [squash] { 'H >- member{'t; 'z} } -->
   [main] sequent ['ext] { 'H >- 'b['z] } -->
   [wf] sequent [squash] { 'H; x: 't >- "type"{'b['x]} } -->
   sequent ['ext] { 'H >- "exists"{'t; v. 'b['v]} }

interactive exists_elim {| elim_resource [] |} 'H 'J 'y 'z :
   [main] sequent ['ext] { 'H; y: 'a; z: 'b['y]; 'J['y, 'z] >- 'C['y, 'z] } -->
   sequent ['ext] { 'H; x: exst v: 'a. 'b['v]; 'J['x] >- 'C['x] }

(************************************************************************
 * DISPLAY FORMS							*
 ************************************************************************)

prec prec_iff
prec prec_implies
prec prec_and
prec prec_or
prec prec_not
prec prec_quant

prec prec_implies < prec_iff
prec prec_iff < prec_or
prec prec_or < prec_and
prec prec_and < prec_not
prec prec_quant < prec_iff

dform true_df1 : mode[src] :: "true" = `"True"

dform false_df1 : mode[src] :: "false" = `"False"

dform not_df1 : mode[src] :: parens :: "prec"[prec_implies] :: "not"{'a} =
   `"not " slot["le"]{'a}

dform implies_df1 : mode[src] :: parens :: "prec"[prec_implies] :: implies{'a; 'b} =
   slot["le"]{'a} `" => " slot["lt"]{'b}

dform iff_df1 : mode[src] :: parens :: "prec"[prec_iff] :: iff{'a; 'b} =
   slot["le"]{'a} `" <==> " slot["lt"]{'b}

dform and_df1 : mode[src] :: parens :: "prec"[prec_and] :: "and"{'a; 'b} =
   slot["le"]{'a} `" or " slot["lt"]{'b}

dform or_df1 : mode[src] :: parens :: "prec"[prec_or] :: "or"{'a; 'b} =
   slot["le"]{'a} `" and " slot["lt"]{'b}

dform all_df1 : mode[src] :: parens :: "prec"[prec_quant] :: "all"{'A; x. 'B} =
   `"all " slot{'x} `": " slot{'A}`"." slot{'B}

dform exists_df1 : mode[src] :: parens :: "prec"[prec_quant] :: "exists"{'A; x. 'B} =
  `"exists " slot{'x} `": " slot{'A} `"." slot{'B}

dform true_df2 : "true" =
   `"True"

dform false_df2 : "false" =
   `"False"

dform not_df2 : parens :: "prec"[prec_not] :: "not"{'a} =
   Nuprl_font!tneg slot["le"]{'a}

dform implies_df2 : parens :: "prec"[prec_implies] :: implies{'a; 'b} =
   slot["le"]{'a} " " Nuprl_font!Rightarrow " " slot["lt"]{'b}

dform iff_df2 : parens :: "prec"[prec_iff] :: iff{'a; 'b} =
   slot["le"]{'a} " " Nuprl_font!Leftrightarrow " " slot["lt"]{'b}

(*
 * Disjunction.
 *)
declare or_df{'a}

dform or_df2 : parens :: "prec"[prec_or] :: "or"{'a; 'b} =
   szone pushm[0] slot["le"]{'a} or_df{'b} popm ezone

dform or_df3 : or_df{."or"{'a; 'b}} =
   hspace Nuprl_font!vee " " slot["le"]{'a} or_df{'b}

dform or_df4 : or_df{'a} =
   hspace Nuprl_font!vee " " slot{'a}

(*
 * Disjunction.
 *)
declare and_df{'a}

dform and_df2 : parens :: "prec"[prec_and] :: "and"{'a; 'b} =
   szone pushm[0] slot["le"]{'a} and_df{'b} popm ezone

dform and_df3 : and_df{."and"{'a; 'b}} =
   hspace Nuprl_font!wedge " " slot["le"]{'a} and_df{'b}

dform and_df4 : and_df{'a} =
   hspace Nuprl_font!wedge " " slot{'a}

(*
 * Quantifiers.
 *)
dform all_df2 : parens :: "prec"[prec_quant] :: "all"{'A; x. 'B} =
   pushm[3] Nuprl_font!forall slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm

dform exists_df2 : parens :: "prec"[prec_quant] :: "exists"{'A; x. 'B} =
   pushm[3] Nuprl_font!"exists" slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let true_term = << "true" >>
let true_opname = opname_of_term true_term
let is_true_term = is_no_subterms_term true_opname

let false_term = << "false" >>
let false_opname = opname_of_term false_term
let is_false_term = is_no_subterms_term false_opname

let all_term = << all x: 'A. 'B['x] >>
let all_opname = opname_of_term all_term
let is_all_term = is_dep0_dep1_term all_opname
let dest_all = dest_dep0_dep1_term all_opname
let mk_all_term = mk_dep0_dep1_term all_opname

let exists_term = << exst x: 'A. 'B['x] >>
let exists_opname = opname_of_term exists_term
let is_exists_term = is_dep0_dep1_term exists_opname
let dest_exists = dest_dep0_dep1_term exists_opname
let mk_exists_term = mk_dep0_dep1_term exists_opname

let or_term = << 'A or 'B >>
let or_opname = opname_of_term or_term
let is_or_term = is_dep0_dep0_term or_opname
let dest_or = dest_dep0_dep0_term or_opname
let mk_or_term = mk_dep0_dep0_term or_opname

let and_term = << 'A and 'B >>
let and_opname = opname_of_term and_term
let is_and_term = is_dep0_dep0_term and_opname
let dest_and = dest_dep0_dep0_term and_opname
let mk_and_term = mk_dep0_dep0_term and_opname

let cor_term = << "cor"{'A; 'B} >>
let cor_opname = opname_of_term cor_term
let is_cor_term = is_dep0_dep0_term cor_opname
let dest_cor = dest_dep0_dep0_term cor_opname
let mk_cor_term = mk_dep0_dep0_term cor_opname

let cand_term = << "cand"{'A; 'B} >>
let cand_opname = opname_of_term cand_term
let is_cand_term = is_dep0_dep0_term cand_opname
let dest_cand = dest_dep0_dep0_term cand_opname
let mk_cand_term = mk_dep0_dep0_term cand_opname

let implies_term = << 'A => 'B >>
let implies_opname = opname_of_term implies_term
let is_implies_term = is_dep0_dep0_term implies_opname
let dest_implies = dest_dep0_dep0_term implies_opname
let mk_implies_term = mk_dep0_dep0_term implies_opname

let iff_term = << "iff"{'A; 'B} >>
let iff_opname = opname_of_term iff_term
let is_iff_term = is_dep0_dep0_term iff_opname
let dest_iff = dest_dep0_dep0_term iff_opname
let mk_iff_term = mk_dep0_dep0_term iff_opname

let not_term = << "not"{'a} >>
let not_opname = opname_of_term not_term
let is_not_term = is_dep0_term not_opname
let dest_not = dest_dep0_term not_opname
let mk_not_term = mk_dep0_term not_opname

(*
 * Squash elimination.
 *)
let squash_falseT p =
   false_squash (Sequent.hyp_count_addr p) p

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of true, false.
 *)
let typeinf_resource = Mp_resource.improve typeinf_resource (true_term, infer_univ1)
let typeinf_resource = Mp_resource.improve typeinf_resource (false_term, infer_univ1)

(*
 * Type of quantifiers.
 *)
let typeinf_resource =
   Mp_resource.improve typeinf_resource (all_term, infer_univ_dep0_dep1 dest_all)
let typeinf_resource =
   Mp_resource.improve typeinf_resource (exists_term, infer_univ_dep0_dep1 dest_exists)

let typeinf_resource =
   Mp_resource.improve typeinf_resource (or_term, infer_univ_dep0_dep0 dest_or)
let typeinf_resource =
   Mp_resource.improve typeinf_resource (and_term, infer_univ_dep0_dep0 dest_and)
let typeinf_resource =
   Mp_resource.improve typeinf_resource (implies_term, infer_univ_dep0_dep0 dest_implies)
let typeinf_resource =
   Mp_resource.improve typeinf_resource (iff_term, infer_univ_dep0_dep0 dest_iff)

let typeinf_resource =
   Mp_resource.improve typeinf_resource (not_term, Typeinf.infer_map dest_not)

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

(*
 * Move hyps dependeing on the var to the conclusion.
 *)
let rec intersects vars fv =
   match vars with
      [] ->
         false
    | v :: tl ->
         if List.mem v fv then
            true
         else
            intersects tl fv

let moveToConclVarsT vars p =
   let { sequent_hyps = hyps } = Sequent.explode_sequent p in
   let len = SeqHyp.length hyps in
   let rec collect i vars indices =
      if i > len then
         indices
      else
         match SeqHyp.get hyps (i - 1) with
            Hypothesis (v, hyp) ->
               if (List.mem v vars) or (is_some_var_free vars hyp) then
                  collect (i + 1) (v :: vars) ((i, v, hyp) :: indices)
               else
                  collect (i + 1) vars indices
          | _ ->
               collect (i + 1) vars indices
   in
   let rec tac indices goal =
      match indices with
         (i, v, hyp) :: tl ->
            if is_var_free v goal then
               let goal' = mk_all_term v hyp goal in
                  assertT goal'
                  thenLT [thinT i thenT tac tl goal';
                          withT (mk_var_term v) (dT (len + 1)) (**)
                             thenLT [memberAssumT i; nthHypT (len + 2)]]

            else
               let goal' = mk_implies_term hyp goal in
                  assertT goal'
                  thenLT [thinT i thenT tac tl goal';
                          (dT (len + 1)) thenLT [nthHypT i; nthHypT (-1)]]
       | [] ->
            idT
   in
      tac (collect 1 vars []) (Sequent.concl p) p

let moveToConclT i p =
   let v, _ = Sequent.nth_hyp p i in
      moveToConclVarsT [v] p

(*
 * Decompose universal formulas.
 *)
let univCDT =
   let rec tac p =
      let concl = Sequent.concl p in
         if is_all_term concl
            or is_dfun_term concl
            or is_implies_term concl
            or is_fun_term concl
         then
            (dT 0 thenMT tac) p
         else
            idT p
   in
      tac

let genUnivCDT =
   let rec tac p =
      let concl = Sequent.concl p in
         if is_all_term concl
            or is_dfun_term concl
            or is_implies_term concl
            or is_fun_term concl
            or is_and_term concl
            or is_prod_term concl
            or is_iff_term concl
         then
            (dT 0 thenMT tac) p
         else
            idT p
   in
      tac

(*
 * Instantiate a hyp with some arguments.
 *)
let instHypT args i =
   let rec inst i firstp args p =
      match args with
         [] ->
            idT p
       | arg :: args' ->
            let _, hyp = Sequent.nth_hyp p i in
            let tailT args =
               if firstp then
                  inst ((Sequent.hyp_count p) + 1) false args
               else
                  thinT i thenT inst i false args
            in
               if is_all_term hyp then
                  (withT arg (dT i) thenMT tailT args') p
               else if is_dfun_term hyp then
                  (withT arg (dT i) thenMT (thinT (-1) thenT tailT args')) p
               else if is_implies_term hyp or is_fun_term hyp then
                  (dT i thenMT tailT args) p
               else
                  raise (RefineError ("instHypT", StringTermError ("hyp is not quantified", hyp)))
   in
      thinningT false (inst i true args)

(*
 * This type is used to collect the arguments to instantiate.
 *)
type formula_args =
   AllTerm of string * term
 | ImpliesTerm
 | IffLeft
 | IffRight

(*
 * Print an info list.
 *)
let eprint_info info =
   let print_item = function
      AllTerm (v, t) ->
         eprintf "\tAllTerm %s: %a\n" v SimplePrint.print_simple_term_fp t
    | ImpliesTerm ->
         eprintf "\tImpliesTerm\n"
    | IffLeft ->
         eprintf "\tIffLeft\n"
    | IffRight ->
         eprintf "\tIffRight\n"
   in
      List.iter print_item info;
      eprintf "\t.%t" eflush

(*
 * Lookup and remove a value from an association list.
 *)
let rec assoc v = function
   (v', t) :: tl ->
      if v' = v then
         t, tl
      else
         let t', tl = assoc v tl in
            t', (v', t) :: tl
 | [] ->
      raise Not_found

(*
 * Check for exact matches.
 *)
let check_subst subst =
   let check (v, t) =
      if !debug_auto then
         eprintf "check_subst: checking %s/%a%t" v SimplePrint.print_simple_term_fp t eflush;
      if not (is_var_term t & dest_var t = v) then
         raise (RefineError ("check_subst", StringError "bad match"))
   in
      List.iter check subst

(*
 * Instantiate the vars with the values in the substitution.
 * If any vars in the subst don't match, they are global,
 * and they should match exactly.
 *)
let instantiate_vars args subst =
   if !debug_auto then
      begin
         let print_subst (v, t) =
            eprintf "\t%s: %a%t" v SimplePrint.print_simple_term_fp t eflush
         in
            eprintf "instantiate_vars: got subst\n";
            List.iter print_subst subst
      end;
   let rec collect result args subst =
      match args with
         [] ->
            check_subst subst;
            result
       | hd::tl ->
            match hd with
               AllTerm (v, t) ->
                  if !debug_auto then
                     eprintf "instantiate_vars: looking for %s%t" v eflush;
                  let t', subst' = assoc v subst in
                     collect (AllTerm (v, t') :: result) tl subst'
             | ImpliesTerm
             | IffLeft
             | IffRight ->
                  collect (hd :: result) tl subst
   in
      collect [] args subst

(*
 * Walk down an implication and look for the goal.
 *)
let rec match_goal args form goal =
   try
      if !debug_auto then
         eprintf "Matching form%t" eflush;
      let subst = match_terms [] form goal in
      let info = instantiate_vars args subst in
         if !debug_auto then
            eprintf "Form matched%t" eflush;
         info
   with
      RefineError _ ->
         if is_all_term form then
            let v, v_T, v_P = dest_all form in
               match_goal (AllTerm (v, v_T) :: args) v_P goal
         else if is_dfun_term form then
            let v, v_T, v_P = dest_dfun form in
               match_goal (AllTerm (v, v_T) :: args) v_P goal
         else if is_implies_term form then
            let v_T, v_P = dest_implies form in
               match_goal (ImpliesTerm :: args) v_P goal
         else if is_fun_term form then
            let v_T, v_P = dest_fun form in
               match_goal (ImpliesTerm :: args) v_P goal
         else if is_iff_term form then
            let left, right = dest_iff form in
               try match_goal (IffLeft :: args) left goal with
                  RefineError _ ->
                     match_goal (IffRight :: args) right goal
         else
            raise (RefineError ("match_goal", StringError "no match"))
    | Not_found ->
         raise (RefineError ("match_goal", StringError "no match"))

(*
 * Try the universal #1.
 *)
let backThruHypT i p =
   if !debug_auto then
      eprintf "Starting backThruHyp %d%t" i eflush;
   let rec tac info i firstp p =
      (match info with
          [] ->
             nthHypT i
        | hd :: args ->
             if !debug_auto then
                eprintf "\tbackThruHyp step%t" eflush;
             let tailT =
                if firstp then
                   [idT; tac args ((Sequent.hyp_count p) + 1) false]
                else
                   [thinT i; thinT i thenT tac args i false]
             in
                match hd with
                   ImpliesTerm ->
                      dT i thenLT tailT
                 | IffRight ->
                      dT i thenT thinT (i + 1) thenT dT i thenLT tailT
                 | IffLeft ->
                      dT i thenT thinT i thenT dT i thenLT tailT
                 | AllTerm (v, t) ->
                      withT t (dT i) thenLT tailT) p
   in
   let _, hyp = Sequent.nth_hyp p i in
   let goal = Sequent.concl p in
   let info = match_goal [] hyp goal in
      if !debug_auto then
         begin
            eprintf "backThruHyp %d%t" i eflush;
            eprint_info info
         end;
      thinningT false (tac info i true) p

(*
 * We can also backchain through assumptions by pulling them
 * in as universally quantified formulas.
 * We assum that we can thin enough.
 *
 * This next function adds the assumption as a universlly
 * quantified formula.
 *)
let assumT i p =
   let goal, assums = dest_msequent (Sequent.msequent p) in
   let assum = List.nth assums (i - 1) in
   let len = TermMan.num_hyps assum in

   (*
    * Compute the number of matching hyps.
    * This is approximate.  Right now, we look
    * for the last context hyp.
    *)
   let rec last_match last_con hyp_index hyps =
      if hyp_index > len then
         last_con
      else
         match SeqHyp.get hyps (hyp_index - 1) with
            Hypothesis _ ->
               last_match last_con (hyp_index + 1) hyps
          | Context _ ->
               last_match (hyp_index + 1) (hyp_index + 1) hyps
   in
   let { sequent_hyps = hyps } = TermMan.explode_sequent assum in
   let index = last_match 1 1 hyps in
   let _ =
      if !debug_auto then
         eprintf "Last_match: %d%t" index eflush
   in

   (* Construct the assumption as a universal formula *)
   let rec collect j =
      if j > len then
         TermMan.nth_concl assum 1
      else
         let v, hyp = TermMan.nth_hyp assum j in
         let goal = collect (j + 1) in
            if is_var_free v goal then
               mk_all_term v hyp goal
            else
               mk_implies_term hyp goal
   in
   let form = collect index in
   let _ =
      if !debug_auto then
         eprintf "Found assumption: %a%t" debug_print form eflush
   in

   (* Call intro form on each arg *)
   let rec introT j p =
      if j > len then
         let goal, assums = dest_msequent (Sequent.msequent p) in
         let assum = List.nth assums (i - 1) in
            if is_squash_sequent goal then
               if is_squash_sequent assum then
                  nthAssumT i p
               else
                  (unsquashT (get_squash_arg assum) thenT nthAssumT i) p
            else
               nthAssumT i p
      else
         (dT 0 thenMT introT (j + 1)) p
   in
      (assertT form
       thenLT [thinAllT index (TermMan.num_hyps goal) thenT introT index;
               addHiddenLabelT "main"]) p

(*
 * Now try backchaining through the assumption.
 *)
let backThruAssumT i p =
   let j = Sequent.hyp_count p + 1 in
      (assumT i thenMT (backThruHypT j thenT thinT j)) p

(*
 * Generalize on a membership assumption:
 *         i. sequent [...] { ... >- member{T; t} } -->
 *         ...
 *         sequent [...] { ... >- 'T2 }
 *         BY genAssumT [i; and any others you want to include...]
 *
 *         sequent [...] { ... >- all x: T. ...others... => T2 }
 *)
let genAssumT indices p =
   let goal, assums = dest_msequent (Sequent.msequent p) in
   let len = List.length assums in
   let _ =
      List.iter (fun i ->
            if i <= 0 || i > len then
               raise (RefineError ("genAssumT", StringIntError ("assum index is out of range", i)))) indices
   in
   let rec make_gen_term t = function
      [] ->
         t
    | i :: indices ->
         let t = make_gen_term t indices in
         let t' = TermMan.nth_concl (List.nth assums (pred i)) 1 in
         if is_member_term t' then
            let t_type, t_var = dest_member t' in
               if is_var_term t_var then
                  mk_all_term (dest_var t_var) t_type t
               else
                  let v = maybe_new_vars1 p "v" in
                     mk_all_term v t_type (var_subst t t_var v)
         else mk_implies_term t' t
   in
   let t = make_gen_term (TermMan.nth_concl goal 1) indices in
   (assertT t thenMT (backThruHypT (-1) thenT autoT) ) p

(************************************************************************
 * AUTO TACTIC                                                          *
 ************************************************************************)

(*
 * In auto tactic, Ok to decompose product hyps.
 *)
let logic_trivT i p =
   let _, hyp = Sequent.nth_hyp p i in
      if is_void_term hyp or is_false_term hyp then
         dT i p
      else
         raise (RefineError ("logic_trivT", StringTermError ("nothing known about", hyp)))

let trivial_resource =
   Mp_resource.improve trivial_resource (**)
      { auto_name = "logic_trivT";
        auto_prec = trivial_prec;
        auto_tac = onSomeHypT logic_trivT
      }

(*
 * Backchaining in auto tactic.
 *)
let logic_autoT i p =
   let _, hyp = Sequent.nth_hyp p i in
      if is_and_term hyp
         or is_prod_term hyp
         or is_dprod_term hyp
         or is_exists_term hyp
      then
         dT i p
      else
         raise (RefineError ("logic_autoT", StringError "unknown formula"))

let logic_prec = create_auto_prec [trivial_prec] []
let back_hyp_prec = create_auto_prec [logic_prec] []
let back_assum_prec = create_auto_prec [back_hyp_prec] []

let auto_resource =
   Mp_resource.improve auto_resource (**)
      { auto_name = "logic_autoT";
        auto_prec = logic_prec;
        auto_tac = auto_wrap (onSomeHypT logic_autoT)
      }

let auto_resource =
   Mp_resource.improve auto_resource (**)
      { auto_name = "backThruHypT";
        auto_prec = back_hyp_prec;
        auto_tac = auto_hyp_progress (fun _ _ -> true) backThruHypT
      }

(*
 * Quick test on assumptions.
 *)
let assum_test i p =
   let goal, assums = dest_msequent (Sequent.msequent p) in
   let goal = TermMan.nth_concl goal 1 in
   let assum = List.nth assums (i - 1) in
   let goal' = TermMan.nth_concl assum 1 in
      try let _ = match_terms [] goal' goal in
         true
      with RefineError _ ->
         false

let auto_resource =
   Mp_resource.improve auto_resource (**)
      { auto_name = "backThruSomeAssumT";
        auto_prec = back_assum_prec;
        auto_tac = auto_assum_progress assum_test backThruAssumT
      }

(************ logic instance for j-prover in refiner/reflib/jall.ml  **********)

module Itt_JLogic =
struct
   open Jlogic_sig

   let is_all_term = is_all_term
   let dest_all = dest_all
   let is_exists_term = is_exists_term
   let dest_exists = dest_exists
   let is_and_term = is_and_term
   let dest_and = dest_and
   let is_or_term = is_or_term
   let dest_or = dest_or
   let is_implies_term = is_implies_term
   let dest_implies = dest_implies
   let is_not_term = is_not_term
   let dest_not = dest_not

   type inference = (term_subst -> tactic) list
   let empty_inf = []
   
   let find_hyp_exn = RefineError("find_hyp_exn", StringError "not found")

   let tryfind_hyp term tact i p =
      match Sequent.nth_hyp p i with
         (_,t) when alpha_equal t term -> tact i p
       | _ -> raise find_hyp_exn
      
   let find_hyp term tact = onSomeHypT (tryfind_hyp term tact)

   let tryappend_subst subst t tact i p =
      tact (match_terms subst t (snd (Sequent.nth_hyp p i))) p

   let append_subst subst t v tact = 
      match (dest_term t).term_terms with
         [_;bt] ->
            let bt = dest_bterm bt in
            begin match bt.bvars with
               [dv] ->
                  onSomeHypT (tryappend_subst subst (subst1 bt.bterm dv v) tact)
             | _ -> raise (Invalid_argument "Itt_logic.append_subst")
            end
       | _ -> raise (Invalid_argument "Itt_logic.append_subst")

   let goal_append_subst subst t v tact p = 
      match (dest_term t).term_terms with
         [_;bt] ->
            let bt = dest_bterm bt in
            begin match bt.bvars with
               [dv] ->
                  tact (match_terms subst (subst1 bt.bterm dv v) (Sequent.concl p)) p
             | _ -> raise (Invalid_argument "Itt_logic.append_subst")
            end
       | _ -> raise (Invalid_argument "Itt_logic.append_subst")

   let append_inf inf hyp inst_term r =
      match r, inf with
         Ax,  _ -> (fun _ -> onSomeHypT nthHypT) :: inf
       | Andl,t::ts -> (fun subst -> (find_hyp (apply_subst hyp subst) dT) thenT t subst) :: ts
       | Negl,t::ts -> (fun subst -> (find_hyp (apply_subst hyp subst) dT) thenT t subst) :: ts
       | Orl, t1::t2::ts ->
            (fun subst ->
               (find_hyp (apply_subst hyp subst) dT) thenLT [t1 subst; t2 subst])
            :: ts
       | Impl,t1::t2::ts ->
            (fun subst ->
               (find_hyp (apply_subst hyp subst) dT) thenLT [t1 subst; t2 subst])
            :: ts
       | Andr,t1::t2::ts -> (fun subst -> dT 0 thenLT [t1 subst; t2 subst]) :: ts
       | Orr1,t::ts -> (fun subst -> selT 1 (dT 0) thenLT [idT; t subst]) :: ts
       | Orr2,t::ts -> (fun subst -> selT 2 (dT 0) thenLT [idT; t subst]) :: ts
       | Impr,t::ts -> (fun subst -> dT 0 thenLT [idT; t subst]) :: ts
       | Negr,t::ts -> (fun subst -> dT 0 thenLT [idT; t subst]) :: ts
       | Exr, t::ts ->
            (fun subst ->
               withT (apply_subst inst_term subst) (dT 0) thenLT [idT; t subst; idT]) :: ts
       | Alll,t::ts ->
            (fun subst ->
               withT (apply_subst inst_term subst) (find_hyp (apply_subst hyp subst) dT)
               thenLT [idT; t subst])
            :: ts
       | Exl, t::ts ->
            (fun subst ->
               (find_hyp hyp dT) thenT
               append_subst subst (apply_subst hyp subst) inst_term t)
            :: ts
       | Allr,t::ts ->
            (fun subst ->
               dT 0 thenLT [idT;goal_append_subst subst (apply_subst hyp subst) inst_term t])
            :: ts
    (* | Orr, ->  *)
       | Fail,_ -> raise (RefineError("Itt_JLogic.create_inf", StringError "failed"))
       | _ -> raise (Invalid_argument "Itt_JLogic.create_inf")
end

module ITT_JProver = Jall.JProver(Itt_JLogic)

let rec filter_hyps = function
   [] -> []
 | Context _ :: hs -> filter_hyps hs
 | Hypothesis (_, h) :: hs -> h :: filter_hyps hs

(* input a list_term of hyps,concl *)
let jproverT p = 
   let seq = explode_sequent (Sequent.goal p) in
   match
      ITT_JProver.prover (filter_hyps (SeqHyp.to_list seq.sequent_hyps)) (SeqGoal.get seq.sequent_goals 0)
   with
      [t] -> t [] p
    | _ -> raise (Invalid_argument "Problems decoding ITT_JProver.prover proof")

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
