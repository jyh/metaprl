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

open Tacticals
open Conversionals
open Sequent
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
   if !debug_load then
      eprintf "Loading Itt_logic%t" eflush

let debug_auto =
   create_debug (**)
      { debug_name = "auto";
        debug_description = "Display auto tactic operations";
        debug_value = false
      }

(************************************************************************
 * REWRITES								*
 ************************************************************************)

declare "prop"[@i:l]

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

primrw unfoldProp : "prop"[@i:l] <--> "univ"[@i:l]

primrw unfoldTrue : "true" <--> unit
primrw unfoldFalse : "false" <--> void
primrw unfoldNot : not{'a} <--> 'a -> void
primrw unfoldImplies : 'a => 'b <--> 'a -> 'b
primrw unfoldIff : "iff"{'a; 'b} <--> (('a -> 'b) & ('b -> 'a))
primrw unfoldAnd : 'a & 'b <--> 'a * 'b
primrw unfoldOr : 'a or 'b <--> 'a + 'b
primrw unfoldCand : "cand"{'a; 'b} <--> 'a & 'b
primrw unfoldCor : "cor"{'a; 'b} <--> "or"{'a; ."cand"{."not"{'a}; 'b}}
primrw unfoldAll : all x: 'A. 'B['x] <--> x:'A -> 'B['x]
primrw unfoldExists : exst x: 'A. 'B['x] <--> x:'A * 'B['x]

primrw reducePropTrue : "prop"["true":t] <--> "true"
primrw reducePropFalse : "prop"["false":t] <--> "false"

let foldTrue    = makeFoldC << "true" >> unfoldTrue
let foldFalse   = makeFoldC << "false" >> unfoldFalse
let foldNot     = makeFoldC << not{'a} >> unfoldNot
let foldImplies = makeFoldC << 'a => 'b >> unfoldImplies
let foldIff     = makeFoldC << "iff"{'a; 'b} >> unfoldIff
let foldAnd     = makeFoldC << 'a & 'b >> unfoldAnd
let foldOr      = makeFoldC << 'a or 'b >> unfoldOr
let foldCand    = makeFoldC << "cand"{'a; 'b} >> unfoldCand
let foldCor     = makeFoldC << "cor"{'a; 'b} >> unfoldCor
let foldAll     = makeFoldC << all x: 'A. 'B['x] >> unfoldAll
let foldExists  = makeFoldC << exst x: 'A. 'B['x] >> unfoldExists

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * True and false.
 *)
interactive true_univ 'H : :
   sequent ['ext] { 'H >- "true" = "true" in univ[@i:l] }

interactive true_type 'H : :
   sequent ['ext] { 'H >- "type"{."true"} }

interactive true_intro 'H : :
   sequent ['ext] { 'H >- "true" }

interactive false_univ 'H : :
   sequent ['ext] { 'H >- "false" = "false" in univ[@i:l] }

interactive false_type 'H : :
   sequent ['ext] { 'H >- "type"{."false"} }

interactive false_elim 'H 'J : :
   sequent ['ext] { 'H; x: "false"; 'J['x] >- 'C['x] }

(*
 * Negation.
 *)
interactive not_univ 'H :
   sequent [squash] { 'H >- 't1 = 't2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- "not"{'t1} = "not"{'t2} in univ[@i:l] }

interactive not_type 'H :
   sequent [squash] { 'H >- "type"{'t} } -->
   sequent ['ext] { 'H >- "type"{."not"{'t}} }

interactive not_intro 'H 'x :
   sequent [squash] { 'H >- "type"{'t} } -->
   sequent ['ext] { 'H; x: 't >- "false" } -->
   sequent ['ext] { 'H >- "not"{'t} }

interactive not_elim 'H 'J :
   sequent ['ext] { 'H; x: "not"{'t}; 'J['x] >- 't } -->
   sequent ['ext] { 'H; x: "not"{'t}; 'J['x] >- 'C }

(*
 * Conjunction.
 *)
interactive and_univ 'H :
   sequent [squash] { 'H >- 'a1 = 'b1 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'a2 = 'b2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- "and"{'a1; 'a2} = "and"{'b1; 'b2} in univ[@i:l] }

interactive and_type 'H :
   sequent [squash] { 'H >- "type"{'a1} } -->
   sequent [squash] { 'H >- "type"{'a2} } -->
   sequent ['ext] { 'H >- "type"{."and"{'a1; 'a2}} }

interactive and_intro 'H :
   sequent ['ext] { 'H >- 'a1 } -->
   sequent ['ext] { 'H >- 'a2 } -->
   sequent ['ext] { 'H >- "and"{'a1; 'a2} }

interactive and_elim 'H 'J 'y 'z :
   sequent ['ext] { 'H; y: 'a1; z: 'a2; 'J['y, 'z] >- 'C['y, 'z] } -->
   sequent ['ext] { 'H; x: "and"{'a1; 'a2}; 'J['x] >- 'C['x] }

(*
 * Disjunction.
 *)
interactive or_univ 'H :
   sequent [squash] { 'H >- 'a1 = 'b1 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'a2 = 'b2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- "or"{'a1; 'a2} = "or"{'b1; 'b2} in univ[@i:l] }

interactive or_type 'H :
   sequent [squash] { 'H >- "type"{'a1} } -->
   sequent [squash] { 'H >- "type"{'a2} } -->
   sequent ['ext] { 'H >- "type"{."or"{'a1; 'a2}} }

interactive or_intro_left 'H :
   sequent [squash] { 'H >- "type"{.'a2} } -->
   sequent ['ext] { 'H >- 'a1 } -->
   sequent ['ext] { 'H >- "or"{'a1; 'a2} }

interactive or_intro_right 'H :
   sequent [squash] { 'H >- "type"{.'a1} } -->
   sequent ['ext] { 'H >- 'a2 } -->
   sequent ['ext] { 'H >- "or"{'a1; 'a2} }

interactive or_elim 'H 'J 'y :
   sequent ['ext] { 'H; y: 'a1; 'J[inl{'y}] >- 'C[inl{'y}] } -->
   sequent ['ext] { 'H; y: 'a2; 'J[inr{'y}] >- 'C[inr{'y}] } -->
   sequent ['ext] { 'H; x: "or"{'a1; 'a2}; 'J['x] >- 'C['x] }

(*
 * Implication.
 *)
interactive implies_univ 'H :
   sequent [squash] { 'H >- 'a1 = 'b1 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'a2 = 'b2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- "implies"{'a1; 'a2} = "implies"{'b1; 'b2} in univ[@i:l] }

interactive implies_type 'H :
   sequent [squash] { 'H >- "type"{'a1} } -->
   sequent [squash] { 'H >- "type"{'a2} } -->
   sequent ['ext] { 'H >- "type"{."implies"{'a1; 'a2}} }

interactive implies_intro 'H 'x :
   sequent [squash] { 'H >- "type"{'a1} } -->
   sequent ['ext] { 'H; x: 'a1 >- 'a2 } -->
   sequent ['ext] { 'H >- "implies"{'a1; 'a2} }

interactive implies_elim 'H 'J 'y :
   sequent ['ext] { 'H; x: "implies"{'a1; 'a2}; 'J['x] >- 'a1 } -->
   sequent ['ext] { 'H; x: "implies"{'a1; 'a2}; 'J['x]; y: 'a2 >- 'C['x] } -->
   sequent ['ext] { 'H; x: "implies"{'a1; 'a2}; 'J['x] >- 'C['x] }

(*
 * Bi-implication.
 *)
interactive iff_univ 'H :
   sequent [squash] { 'H >- 'a1 = 'b1 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'a2 = 'b2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- "iff"{'a1; 'a2} = "iff"{'b1; 'b2} in univ[@i:l] }

interactive iff_type 'H :
   sequent [squash] { 'H >- "type"{'a1} } -->
   sequent [squash] { 'H >- "type"{'a2} } -->
   sequent ['ext] { 'H >- "type"{."iff"{'a1; 'a2}} }

interactive iff_intro 'H :
   sequent ['ext] { 'H >- 'a1 => 'a2 } -->
   sequent ['ext] { 'H >- 'a2 => 'a1 } -->
   sequent ['ext] { 'H >- "iff"{'a1; 'a2} }

interactive iff_elim 'H 'J 'y 'z :
   sequent ['ext] { 'H; y: "implies"{'a1; 'a2}; z: "implies"{'a2; 'a1}; 'J['y, 'z] >- 'C['y, 'z] } -->
   sequent ['ext] { 'H; x: "iff"{'a1; 'a2}; 'J['x] >- 'C['x] }

(*
 * Conjunction.
 *)
interactive cand_univ 'H 'x :
   sequent [squash] { 'H >- 'a1 = 'b1 in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'a1 >- 'a2 = 'b2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- "cand"{'a1; 'a2} = "cand"{'b1; 'b2} in univ[@i:l] }

interactive cand_type 'H 'x :
   sequent [squash] { 'H >- "type"{'a1} } -->
   sequent [squash] { 'H; x: 'a1 >- "type"{'a2} } -->
   sequent ['ext] { 'H >- "type"{."cand"{'a1; 'a2}} }

interactive cand_intro 'H 'x :
   sequent ['ext] { 'H >- 'a1 } -->
   sequent ['ext] { 'H; x: 'a1 >- 'a2 } -->
   sequent ['ext] { 'H >- "cand"{'a1; 'a2} }

interactive cand_elim 'H 'J 'y 'z :
   sequent ['ext] { 'H; y: 'a1; z: 'a2; 'J['y, 'z] >- 'C['y, 'z] } -->
   sequent ['ext] { 'H; x: "cand"{'a1; 'a2}; 'J['x] >- 'C['x] }

(*
 * Disjunction.
 *)
interactive cor_univ 'H 'x :
   sequent [squash] { 'H >- 'a1 = 'b1 in univ[@i:l] } -->
   sequent [squash] { 'H; x: "not"{'a1} >- 'a2 = 'b2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- "cor"{'a1; 'a2} = "cor"{'b1; 'b2} in univ[@i:l] }

interactive cor_type 'H 'x :
   sequent [squash] { 'H >- "type"{'a1} } -->
   sequent [squash] { 'H; x: "not"{'a1} >- "type"{'a2} } -->
   sequent ['ext] { 'H >- "type"{."cor"{'a1; 'a2}} }

interactive cor_intro_left 'H 'x :
   sequent [squash] { 'H; x: "not"{'a1} >- "type"{.'a2} } -->
   sequent ['ext] { 'H >- 'a1 } -->
   sequent ['ext] { 'H >- "cor"{'a1; 'a2} }

interactive cor_intro_right 'H 'x :
   sequent [squash] { 'H >- "type"{.'a1} } -->
   sequent ['ext] { 'H >- "not"{'a1} } -->
   sequent ['ext] { 'H; x: "not"{'a1} >- 'a2 } -->
   sequent ['ext] { 'H >- "cor"{'a1; 'a2} }

interactive cor_elim 'H 'J 'u 'v :
   sequent ['ext] { 'H; u: 'a1; 'J[inl{'u}] >- 'C[inl{'u}] } -->
   sequent ['ext] { 'H; u: "not"{'a1}; v: 'a2; 'J[inr{'u, 'v}] >- 'C[inr{'u, 'v}] } -->
   sequent ['ext] { 'H; x: "cor"{'a1; 'a2}; 'J['x] >- 'C['x] }

(*
 * All elimination performs a thinning
 *)
interactive all_univ 'H 'x :
   sequent [squash] { 'H >- 't1 = 't2 in univ[@i:l] } -->
   sequent [squash] { 'H; x : 't1 >- 'b1['x] = 'b2['x] in univ[@i:l] } -->
   sequent ['ext] { 'H >- "all"{'t1; x1. 'b1['x1]} = "all"{'t2; x2. 'b2['x2]} in univ[@i:l] }

interactive all_type 'H 'x :
   sequent [squash] { 'H >- "type"{'t} } -->
   sequent [squash] { 'H; x: 't >- "type"{'b['x]} } -->
   sequent ['ext] { 'H >- "type"{."all"{'t; v. 'b['v]}} }

interactive all_intro 'H 'x :
   sequent [squash] { 'H >- "type"{'t} } -->
   sequent ['ext] { 'H; x: 't >- 'b['x] } -->
   sequent ['ext] { 'H >- "all"{'t; v. 'b['v]} }

interactive all_elim 'H 'J 'w 'z :
   sequent [squash] { 'H; x: all a: 'A. 'B['a]; 'J['x] >- 'z = 'z in 'A } -->
   sequent ['ext] { 'H; x: all a: 'A. 'B['a]; 'J['x]; w: 'B['z] >- 'C['x] } -->
   sequent ['ext] { 'H; x: all a: 'A. 'B['a]; 'J['x] >- 'C['x] }

(*
 * Existential.
 *)
interactive exists_univ 'H 'x :
   sequent [squash] { 'H >- 't1 = 't2 in univ[@i:l] } -->
   sequent [squash] { 'H; x : 't1 >- 'b1['x] = 'b2['x] in univ[@i:l] } -->
   sequent ['ext] { 'H >- "exists"{'t1; x1. 'b1['x1]} = "exists"{'t2; x2. 'b2['x2]} in univ[@i:l] }

interactive exists_type 'H 'x :
   sequent [squash] { 'H >- "type"{'t} } -->
   sequent [squash] { 'H; x: 't >- "type"{'b['x]} } -->
   sequent ['ext] { 'H >- "type"{."exists"{'t; v. 'b['v]}} }

interactive exists_intro 'H 'z 'x :
   sequent [squash] { 'H >- 'z = 'z in 't } -->
   sequent ['ext] { 'H >- 'b['z] } -->
   sequent [squash] { 'H; x: 't >- "type"{'b['x]} } -->
   sequent ['ext] { 'H >- "exists"{'t; v. 'b['v]} }

interactive exists_elim 'H 'J 'y 'z :
   sequent ['ext] { 'H; y: 'a; z: 'b['y]; 'J['y, 'z] >- 'C['y, 'z] } -->
   sequent ['ext] { 'H; x: exst v: 'a. 'b['v]; 'J['x] >- 'C['x] }

(************************************************************************
 * DISPLAY FORMS							*
 ************************************************************************)

prec prec_iff
prec prec_implies
prec prec_and
prec prec_or
prec prec_quant

prec prec_implies < prec_iff
prec prec_iff < prec_or
prec prec_or < prec_and
prec prec_quant < prec_iff

dform true_df1 : mode[src] :: "true" = `"True"

dform false_df1 : mode[src] :: "false" = `"False"

dform not_df1 : mode[src] :: parens :: "prec"[prec_implies] :: "not"{'a} =
   `"not " slot[le]{'a}

dform implies_df1 : mode[src] :: parens :: "prec"[prec_implies] :: implies{'a; 'b} =
   slot[le]{'a} `" => " slot[lt]{'b}

dform iff_df1 : mode[src] :: parens :: "prec"[prec_iff] :: iff{'a; 'b} =
   slot[le]{'a} `" <==> " slot[lt]{'b}

dform and_df1 : mode[src] :: parens :: "prec"[prec_and] :: "and"{'a; 'b} =
   slot[le]{'a} `" /\\ " slot[lt]{'b}

dform or_df1 : mode[src] :: parens :: "prec"[prec_or] :: "or"{'a; 'b} =
   slot[le]{'a} `" \\/ " slot[lt]{'b}

dform all_df1 : mode[src] :: parens :: "prec"[prec_quant] :: "all"{'A; x. 'B} =
   `"all " slot{'x} `": " slot{'A}`"." slot{'B}

dform exists_df1 : mode[src] :: parens :: "prec"[prec_quant] :: "exists"{'A; x. 'B} =
  `"exists " slot{'x} `": " slot{'A} `"." slot{'B}

dform true_df2 : mode[prl] :: "true" =
   `"True"

dform false_df2 : mode[prl] :: "false" =
   `"False"

dform not_df2 : mode[prl] :: parens :: "prec"[prec_implies] :: "not"{'a} =
   Nuprl_font!tneg slot[le]{'a}

dform implies_df2 : mode[prl] :: parens :: "prec"[prec_implies] :: implies{'a; 'b} =
   slot[le]{'a} " " Nuprl_font!Rightarrow " " slot[lt]{'b}

dform iff_df2 : mode[prl] :: parens :: "prec"[prec_iff] :: iff{'a; 'b} =
   slot[le]{'a} " " Nuprl_font!Leftrightarrow " " slot[lt]{'b}

dform and_df1 : mode[prl] :: parens :: "prec"[prec_and] :: "and"{'a; 'b} =
   slot[le]{'a} " " Nuprl_font!wedge " " slot[lt]{'b}

(*
 * Disjunction.
 *)
declare or_df{'a}

dform or_df2 : mode[prl] :: parens :: "prec"[prec_or] :: "or"{'a; 'b} =
   szone pushm[0] slot{'a} or_df{'b} popm ezone

dform or_df3 : mode[prl] :: or_df{."or"{'a; 'b}} =
   hspace Nuprl_font!vee " " slot{'a} or_df{'b}

dform or_df4 : mode[prl] :: or_df{'a} =
   hspace Nuprl_font!vee " " slot{'a}

(*
 * Quantifiers.
 *)
dform all_df2 : mode[prl] :: parens :: "prec"[prec_quant] :: "all"{'A; x. 'B} =
   pushm[3] Nuprl_font!forall slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm

dform exists_df2 : mode[prl] :: parens :: "prec"[prec_quant] :: "exists"{'A; x. 'B} =
   pushm[3] Nuprl_font!"exists" slot{'x} `":" slot{'A} sbreak["",". "] slot{'B} popm

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let true_term = << "true" >>
let is_true_term t = t = true_term

let false_term = << "false" >>
let is_false_term t = t = false_term

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

(************************************************************************
 * D and EQCD TACTICS                                                   *
 ************************************************************************)

(*
 * "True" tactics.
 *)
let d_trueT i p =
   if i = 0 then
      true_intro (hyp_count_addr p) p
   else
      raise (RefineError ("d_trueT", StringError "no elimination form (unfold it if you want to elim)"))

let d_resource = d_resource.resource_improve d_resource (true_term, d_trueT)

let eqcd_trueT p =
   true_univ (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (true_term, eqcd_trueT)

let true_equal_term = << "true" = "true" in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (true_equal_term, d_wrap_eqcd eqcd_trueT)

let d_true_typeT i p =
   if i = 0 then
      true_type (hyp_count_addr p) p
   else
      raise (RefineError ("d_true_typeT", StringError "no elimination form"))

let true_type_term = << "type"{."true"} >>

let d_resource = d_resource.resource_improve d_resource (true_type_term, d_true_typeT)

(*
 * "False" tactics.
 *)
let d_falseT i p =
   if i = 0 then
      raise (RefineError ("d_falseT", StringError "no rule to prove false"))
   else
      let j, k = hyp_indices p i in
         false_elim j k p

let d_resource = d_resource.resource_improve d_resource (false_term, d_falseT)

let eqcd_falseT p =
   false_univ (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (false_term, eqcd_falseT)

let false_equal_term = << "false" = "false" in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (false_equal_term, d_wrap_eqcd eqcd_falseT)

let d_false_typeT i p =
   if i = 0 then
      false_type (hyp_count_addr p) p
   else
      raise (RefineError ("d_false_typeT", StringError "no elimination form"))

let false_type_term = << "type"{."false"} >>

let d_resource = d_resource.resource_improve d_resource (false_type_term, d_false_typeT)

(*
 * Tactics for conjunction.
 *)
let d_notT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         (not_intro (hyp_count_addr p) v
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
   else
      let j, k = hyp_indices p i in
         not_elim j k p

let d_resource = d_resource.resource_improve d_resource (not_term, d_notT)

let eqcd_notT p =
   not_univ (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (not_term, eqcd_notT)

let not_equal_term = << "not"{'t1} = "not"{'t2} in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (not_equal_term, d_wrap_eqcd eqcd_notT)

let d_not_typeT i p =
   if i = 0 then
      (not_type (hyp_count_addr p) thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_not_typeT", StringError "no elimination form"))

let not_type_term = << "type"{."not"{'t1}} >>

let d_resource = d_resource.resource_improve d_resource (not_type_term, d_not_typeT)

(*
 * Tactics for conjunction.
 *)
let d_andT i p =
   if i = 0 then
      and_intro (hyp_count_addr p) p
   else
      let u, v = maybe_new_vars2 p "u" "v" in
      let j, k = hyp_indices p i in
         and_elim j k u v p

let d_resource = d_resource.resource_improve d_resource (and_term, d_andT)

let eqcd_andT p =
   and_univ (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (and_term, eqcd_andT)

let and_equal_term = << "and"{'t1; 't2} = "and"{'t3; 't4} in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (and_equal_term, d_wrap_eqcd eqcd_andT)

let d_and_typeT i p =
   if i = 0 then
      (and_type (hyp_count_addr p) thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_and_typeT", StringError "no elimination form"))

let and_type_term = << "type"{."and"{'t1; 't2}} >>

let d_resource = d_resource.resource_improve d_resource (and_type_term, d_and_typeT)

(*
 * Tactics for disjunction.
 *)
let d_orT i p =
   if i = 0 then
      let arg = get_sel_arg p in
      let tac =
         if arg = 1 then
            or_intro_left
         else
            or_intro_right
      in
         (tac (hyp_count_addr p)
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
   else
      let v, _ = nth_hyp p i in
      let j, k = hyp_indices p i in
         or_elim j k v p

let d_resource = d_resource.resource_improve d_resource (or_term, d_orT)

let eqcd_orT p =
   or_univ (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (or_term, eqcd_orT)

let or_equal_term = << "or"{'t1; 't2} = "or"{'t3; 't4} in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (or_equal_term, d_wrap_eqcd eqcd_orT)

let d_or_typeT i p =
   if i = 0 then
      (or_type (hyp_count_addr p) thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_or_typeT", StringError "no elimination form"))

let or_type_term = << "type"{."or"{'t1; 't2}} >>

let d_resource = d_resource.resource_improve d_resource (or_type_term, d_or_typeT)

(*
 * Tactics for conditional conjunction.
 *)
let d_candT i p =
   if i = 0 then
      let u = maybe_new_vars1 p "u" in
         cand_intro (hyp_count_addr p) u p
   else
      let u, v = maybe_new_vars2 p "u" "v" in
      let j, k = hyp_indices p i in
         cand_elim j k u v p

let d_resource = d_resource.resource_improve d_resource (cand_term, d_candT)

let eqcd_candT p =
   let u = maybe_new_vars1 p "u" in
      cand_univ (hyp_count_addr p) u p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (cand_term, eqcd_candT)

let cand_equal_term = << "cand"{'t1; 't2} = "cand"{'t3; 't4} in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (cand_equal_term, d_wrap_eqcd eqcd_candT)

let d_cand_typeT i p =
   if i = 0 then
      let u = maybe_new_vars1 p "u" in
         (cand_type (hyp_count_addr p) u thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_cand_typeT", StringError "no elimination form"))

let cand_type_term = << "type"{."cand"{'t1; 't2}} >>

let d_resource = d_resource.resource_improve d_resource (cand_type_term, d_cand_typeT)

(*
 * Tactics for implication.
 *)
let d_impliesT i p =
      let v = maybe_new_vars1 p "v" in
   if i = 0 then
         (implies_intro (hyp_count_addr p) v
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
   else
      let j, k = hyp_indices p i in
         (implies_elim j k v
          thenLT [addHiddenLabelT "antecedent";
                  addHiddenLabelT "main"]) p

let d_resource = d_resource.resource_improve d_resource (implies_term, d_impliesT)

let eqcd_impliesT p =
   implies_univ (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (implies_term, eqcd_impliesT)

let implies_equal_term = << "implies"{'t1; 't2} = "implies"{'t3; 't4} in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (implies_equal_term, d_wrap_eqcd eqcd_impliesT)

let d_implies_typeT i p =
   if i = 0 then
      (implies_type (hyp_count_addr p) thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_implies_typeT", StringError "no elimination form"))

let implies_type_term = << "type"{."implies"{'t1; 't2}} >>

let d_resource = d_resource.resource_improve d_resource (implies_type_term, d_implies_typeT)

(*
 * Tactics for bi-implication.
 *)
let d_iffT i p =
   if i = 0 then
      iff_intro (hyp_count_addr p) p
   else
      let u, v = maybe_new_vars2 p "u" "v" in
      let j, k = hyp_indices p i in
         iff_elim j k u v p

let d_resource = d_resource.resource_improve d_resource (iff_term, d_iffT)

let eqcd_iffT p =
   iff_univ (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (iff_term, eqcd_iffT)

let iff_equal_term = << "iff"{'t1; 't2} = "iff"{'t3; 't4} in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (iff_equal_term, d_wrap_eqcd eqcd_iffT)

let d_iff_typeT i p =
   if i = 0 then
      (iff_type (hyp_count_addr p) thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_iff_typeT", StringError "no elimination form"))

let iff_type_term = << "type"{."iff"{'t1; 't2}} >>

let d_resource = d_resource.resource_improve d_resource (iff_type_term, d_iff_typeT)

(*
 * Special elimination case for all.
 *)
let d_allT i p =
   if i = 0 then
      let goal = Sequent.concl p in
      let v, _, _ = dest_all goal in
      let v = maybe_new_vars1 p "v" in
         all_intro (hyp_count_addr p) v p
   else
      let z = get_with_arg p in
      let j, k = hyp_indices p i in
      let v = Var.maybe_new_vars1 p "v" in
         (all_elim j k v z
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p

let all_term = << all a: 'A. 'B['a] >>

let d_resource = d_resource.resource_improve d_resource (all_term, d_allT)

let eqcd_allT p =
   let goal = Sequent.concl p in
   let _, t, _ = dest_equal goal in
   let v, _, _ = dest_all t in
   let v = maybe_new_vars1 p v in
      (all_univ (hyp_count_addr p) v thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (all_term, eqcd_allT)

let all_equal_term = << (all x1: 't1. 'b1['x1]) = (all x2: 't2. 'b2['t2]) in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (all_equal_term, d_wrap_eqcd eqcd_allT)

let d_all_typeT i p =
   if i = 0 then
      let goal = Sequent.concl p in
      let t = dest_type_term goal in
      let v, _, _ = dest_all t in
      let v = maybe_new_vars1 p v in
         (all_type (hyp_count_addr p) v thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_all_typeT", StringError "no elimination form"))

let all_type_term = << "type"{."all"{'t1; x. 't2['x]}} >>

let d_resource = d_resource.resource_improve d_resource (all_type_term, d_all_typeT)

(*
 * Existential.
 *)
let d_existsT i p =
   if i = 0 then
      let goal = Sequent.concl p in
      let v, _, _ = dest_exists goal in
      let v = maybe_new_vars1 p "v" in
      let z = get_with_arg p in
         (exists_intro (hyp_count_addr p) z v
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main";
                  addHiddenLabelT "wf"]) p
   else
      let _, hyp = nth_hyp p i in
      let v, _, _ = dest_exists hyp in
      let u, v = maybe_new_vars2 p v v in
      let j, k = hyp_indices p i in
         exists_elim j k u v p

let exists_term = << exst a: 'A. 'B['a] >>

let d_resource = d_resource.resource_improve d_resource (exists_term, d_existsT)

let eqcd_existsT p =
   let goal = Sequent.concl p in
   let _, t, _ = dest_equal goal in
   let v, _, _ = dest_exists t in
   let v = maybe_new_vars1 p v in
      (exists_univ (hyp_count_addr p) v thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (exists_term, eqcd_existsT)

let exists_equal_term = << (exst x1: 't1. 'b1['x1]) = (exst x2: 't2. 'b2['t2]) in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (exists_equal_term, d_wrap_eqcd eqcd_existsT)

let d_exists_typeT i p =
   if i = 0 then
      let goal = Sequent.concl p in
      let t = dest_type_term goal in
      let v, _, _ = dest_exists t in
      let v = maybe_new_vars1 p v in
         (exists_type (hyp_count_addr p) v thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_exists_typeT", StringError "no elimination form"))

let exists_type_term = << "type"{."exists"{'t1; x. 't2['x]}} >>

let d_resource = d_resource.resource_improve d_resource (exists_type_term, d_exists_typeT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of true, false.
 *)
let inf_univ1 _ decl _ = decl, univ1_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (true_term, inf_univ1)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (false_term, inf_univ1)

(*
 * Type of quantifiers.
 *)
let inf_d dest f decl t =
   let v, a, b = dest t in
   let decl', a' = f decl a in
   let decl'', b' = f (add_unify_subst v a decl') b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (all_term, inf_d dest_all)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (exists_term, inf_d dest_exists)

(*
 * Type of propositions.
 *)
let inf_nd dest f decl t =
   let a, b = dest t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
   let le1, le2 = dest_univ a', dest_univ b' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (or_term, inf_nd dest_or)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (and_term, inf_nd dest_and)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (implies_term, inf_nd dest_implies)
let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (iff_term, inf_nd dest_iff)

(*
 * Type of all.
 *)
let inf_not f decl t =
   let a = dest_not t in
      f decl a

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (not_term, inf_not)

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
   let { sequent_hyps = hyps } = explode_sequent p in
   let len = SeqHyp.length hyps in
   let rec collect i vars indices =
      if i > len then
         indices
      else
         match SeqHyp.get hyps (i - 1) with
            Hypothesis (v, hyp) ->
               if List.mem v vars or intersects vars (free_vars hyp) then
                  collect (i + 1) (v :: vars) ((i, v, hyp) :: indices)
               else
                  collect (i + 1) vars indices
          | _ ->
               collect (i + 1) vars indices
   in
   let rec tac indices goal =
      match indices with
         (i, v, hyp) :: tl ->
            if is_free_var v goal then
               let goal' = mk_all_term v hyp goal in
                  assertT goal'
                  thenLT [thinT i thenT tac tl goal';
                          withT (mk_var_term v) (dT (len + 1)) (**)
                             thenLT [equalAssumT i; nthHypT (len + 2)]]

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
   let v, _ = nth_hyp p i in
      moveToConclVarsT [v] p

(*
 * Decompose universal formulas.
 *)
let rec univCDT p =
   let concl = Sequent.concl p in
      if is_all_term concl
         or is_dfun_term concl
         or is_implies_term concl
         or is_fun_term concl
      then
         (dT 0 thenMT univCDT) p
      else
         idT p

let rec genUnivCDT p =
   let concl = Sequent.concl p in
      if is_all_term concl
         or is_dfun_term concl
         or is_implies_term concl
         or is_fun_term concl
         or is_and_term concl
         or is_prod_term concl
         or is_iff_term concl
      then
         (dT 0 thenMT genUnivCDT) p
      else
         idT p

(*
 * Instantiate a hyp with some arguments.
 *)
let instHypT args i =
   let rec inst i firstp args p =
      match args with
         [] ->
            idT p
       | arg :: args' ->
            let _, hyp = nth_hyp p i in
            let tailT args =
               if firstp then
                  inst ((hyp_count p) + 1) false args
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
      inst i true args

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
                   [idT; tac args ((hyp_count p) + 1) false]
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
   let _, hyp = nth_hyp p i in
   let goal = Sequent.concl p in
   let info = match_goal [] hyp goal in
      if !debug_auto then
         begin
            eprintf "backThruHyp %d%t" i eflush;
            eprint_info info
         end;
      tac info i true p

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
            if is_free_var v goal then
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
   let j = hyp_count p + 1 in
      (assumT i thenMT (backThruHypT j thenT thinT j)) p

(************************************************************************
 * AUTO TACTIC                                                          *
 ************************************************************************)

(*
 * In auto tactic, Ok to decompose product hyps.
 *)
let logic_trivT i p =
   let _, hyp = nth_hyp p i in
      if is_void_term hyp or is_false_term hyp then
         dT i p
      else
         raise (RefineError ("logic_trivT", StringTermError ("nothing known about", hyp)))

let trivial_resource =
   trivial_resource.resource_improve trivial_resource (**)
      { auto_name = "logic_trivT";
        auto_prec = trivial_prec;
        auto_tac = onSomeHypT logic_trivT
      }

(*
 * Backchaining in auto tactic.
 *)
let logic_autoT i p =
   let _, hyp = nth_hyp p i in
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
   auto_resource.resource_improve auto_resource (**)
      { auto_name = "logic_autoT";
        auto_prec = logic_prec;
        auto_tac = auto_wrap (onSomeHypT logic_autoT)
      }

let auto_resource =
   auto_resource.resource_improve auto_resource (**)
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
      try match_terms [] goal' goal; true with
         RefineError _ ->
            false

let auto_resource =
   auto_resource.resource_improve auto_resource (**)
      { auto_name = "backThruSomeAssumT";
        auto_prec = back_assum_prec;
        auto_tac = auto_assum_progress assum_test backThruAssumT
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
