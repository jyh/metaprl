(*!
 * @spelling{group}
 *
 * @begin[doc]
 * @module[Itt_group]
 *
 * This theory defines groups.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * Author: Xin Yu
 * @email{xiny@cs.caltech.edu}
 * @end[license]
 *)

(*! @doc{@parents} *)
extends Itt_grouplikeobj
(*! @docoff *)
extends Itt_subset

open Printf
open Mp_debug
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

open Itt_struct
open Itt_record
open Itt_fun
open Itt_int_ext
open Itt_isect

let _ =
   show_loading "Loading Itt_group%t"

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * @end[doc]
 *)
define unfold_pregroup1 : pregroup[i:l] <-->
   record["inv":t]{r. 'r^car -> 'r^car; premonoid[i:l]}

define unfold_isGroup : isGroup{'g} <-->
   isSemigroup{'g} & all x: 'g^car. 'g^"1" *['g] 'x = 'x in 'g^car & all x: 'g^car. ('g^inv 'x) *['g] 'x = 'g^"1" in 'g^car

define unfold_group1 : group[i:l] <-->
   {g: pregroup[i:l] | isGroup{'g}}

define unfold_abelg : abelg[i:l] <-->
   {g: group[i:l] | isCommutative{'g}}

define unfold_lcoset : lcoset{'s; 'g; 'b} <-->
   {x: 'g^car | exst a: 's^car. 'x = 'b *['g] 'a in 'g^car}

define unfold_rcoset : rcoset{'s; 'g; 'b} <-->
   {x: 'g^car | exst a: 's^car. 'x = 'a *['g] 'b in 'g^car}

define unfold_normalSubg : normalSubg[i:l]{'s; 'g} <-->
   subStructure{'s; 'g} & all x: 'g^car. lcoset{'s; 'g; 'x} = rcoset{'s; 'g; 'x} in univ[i:l]

define unfold_groupHom : groupHom{'A; 'B} <-->
   { f: 'A^car -> 'B^car | all x: 'A^car. all y: 'A^car. ('f ('x *['A] 'y)) = ('f 'x) *['B] ('f 'y) in 'B^car }
(*! @docoff *)

interactive_rw unfold_pregroup :
   pregroup[i:l] <--> {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car}

interactive_rw unfold_group :
   group[i:l] <--> {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car; (all x: ^car. all y: ^car. all z: ^car. ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^car) & (all x: ^car. ^"1" ^* 'x = 'x in ^car) & (all x: ^car. ((^inv) 'x) ^* 'x = ^"1" in ^car)}

let fold_pregroup1 = makeFoldC << pregroup[i:l] >> unfold_pregroup1
let fold_pregroup = makeFoldC << pregroup[i:l] >> unfold_pregroup
let fold_isGroup = makeFoldC << isGroup{'g} >> unfold_isGroup
let fold_group1 = makeFoldC << group[i:l] >> unfold_group1
let fold_group = makeFoldC << group[i:l] >> unfold_group
let fold_abelg = makeFoldC << abelg[i:l] >> unfold_abelg
let fold_lcoset = makeFoldC << lcoset{'s; 'g; 'b} >> unfold_lcoset
let fold_rcoset = makeFoldC << rcoset{'s; 'g; 'b} >> unfold_rcoset
let fold_normalSubg = makeFoldC << normalSubg[i:l]{'s; 'g} >> unfold_normalSubg
let fold_groupHom = makeFoldC <<groupHom{'A; 'B}  >> unfold_groupHom

let groupDT n = rw unfold_group n thenT dT n
let abelgDT n = rw unfold_abelg n thenT dT n

let resource elim +=
   [<<group[i:l]>>, groupDT;
    <<abelg[i:l]>>, abelgDT
   ]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_inv
prec prec_mul < prec_inv

dform group_df : except_mode[src] :: group[i:l] =
   math_group{slot[i:l]}

dform pregroup_df : except_mode[src] :: pregroup[i:l] =
   math_pregroup{slot[i:l]}

dform isGroup_df : except_mode[src] :: isGroup{'g} =
   `"isGroup(" slot{'g} `")"

dform inv_df1 : except_mode[src] :: parens :: "prec"[prec_inv] :: ('g^inv 'a) =
   math_inv{'g; 'a}

dform abelg_df : except_mode[src] :: abelg[i:l] =
   math_abelg{slot[i:l]}

dform lcoset_df : except_mode[src] :: lcoset{'h; 'g; 'a} =
   math_lcoset{'h; 'g; 'a}

dform rcoset_df : except_mode[src] :: rcoset{'h; 'g; 'a} =
   math_rcoset{'h; 'g; 'a}

dform normalSubg_df : except_mode[src] :: normalSubg[i:l]{'s; 'g} =
   math_normalSubg{slot[i:l]; 's; 'g}

dform groupHom_df : except_mode[src] :: groupHom{'A; 'B} =
   math_groupHom{'A; 'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Well-formedness}
 *
 * @end[doc]
 *)
interactive pregroup_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{pregroup[i:l]} }

interactive group_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{group[i:l]} }

interactive group_elim {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; g: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car}; u: squash{.all x: 'g^car. all y: 'g^car. all z: 'g^car. (('x *['g] 'y) *['g] 'z = 'x *['g] ('y *['g] 'z) in 'g^car)}; v: squash{.all x: 'g^car. 'g^"1" *['g] 'x = 'x in 'g^car}; w: squash{.all x: 'g^car. ('g^inv 'x) *['g] 'x = 'g^"1" in 'g^car}; 'J['g] >- 'C['g] } -->
   sequent ['ext] { 'H; g: group[i:l]; 'J['g] >- 'C['g] }   

interactive isGroup_wf {| intro [intro_typeinf <<'g>>] |} 'H pregroup[i:l] :
   sequent [squash] { 'H >- 'g in pregroup[i:l] } -->
   sequent ['ext] {'H >- "type"{isGroup{'g}} }

interactive car_wf {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- "type"{('g^car)} }

interactive car_wf2 {| intro [] |} 'H :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- 'g^car in univ[i:l] }

interactive op_wf {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- 'g^"*" in 'g^car -> 'g^car -> 'g^car }

interactive inv_wf {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- 'g^inv in 'g^car -> 'g^car }

interactive op_in_G {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent [squash] {'H >- 'b in 'g^car } -->
   sequent ['ext] {'H >- 'a *['g] 'b in 'g^car }

interactive id_in_G {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- 'g^"1" in 'g^car }

interactive inv_in_G {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- 'g^inv 'a in 'g^car }

interactive group_assoc {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent [squash] {'H >- 'b in 'g^car } -->
   sequent [squash] {'H >- 'c in 'g^car } -->
   sequent ['ext] {'H >- ('a *['g] 'b) *['g] 'c = 'a *['g] ('b *['g] 'c) in 'g^car }

interactive group_left_id {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- 'g^"1" *['g] 'a = 'a in 'g^car }

interactive group_left_inv {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- ('g^inv 'a) *['g] 'a = 'g^"1" in 'g^car }
(*! @docoff *)

interactive op_eq1 {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a = 'b in 'g^car } -->
   sequent [squash] {'H >- 'c in 'g^car } -->
   sequent ['ext] {'H >- 'a *['g] 'c = 'b *['g] 'c in 'g^car }

interactive op_eq2 {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a = 'b in 'g^car } -->
   sequent [squash] {'H >- 'c in 'g^car } -->
   sequent ['ext] {'H >- 'c *['g] 'a = 'c *['g] 'b in 'g^car }

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Lemmas}
 *
 * @begin[enumerate]
 * @item{$u * u = u$ implies $u$ is the identity.}
 * @item{The left inverse is also the right inverse.}
 * @item{The left identity is also the right identity.}
 * @end[enumerate]
 * @end[doc]
 *)
interactive id_judge {| elim [elim_typeinf <<'g>>] |} 'H 'J group[i:l] :
   sequent [squash] {'H; x: 'u *['g] 'u = 'u in 'g^car; 'J['x] >- 'g in group[i:l] } -->
   sequent ['ext] {'H; x: 'u *['g] 'u = 'u in 'g^car; 'J['x]; y: 'u = 'g^"1" in 'g^car >- 'C['x] } -->
   sequent ['ext] {'H; x: 'u *['g] 'u = 'u in 'g^car; 'J['x] >- 'C['x] }

interactive right_inv {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- 'a *['g] ('g^inv 'a) = 'g^"1" in 'g^car }

interactive right_id {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- 'a *['g] 'g^"1" = 'a in 'g^car }

(*!
 * @begin[doc]
 * @modsubsection{Theorems}
 *
 * A group is also a monoid.
 * @end[doc]
 *)
interactive group_is_monoid {| intro [AutoMustComplete] |} 'H :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent ['ext] { 'H >- 'g in monoid[i:l] }

(*!
 * @begin[doc]
 *
 * The left and right cancellation laws.
 * @end[doc]
 *)
(* Cancellation: a * b = a * c => b = c *)
interactive cancel_left {| elim [elim_typeinf <<'g>>] |} 'H 'J group[i:l] :
   sequent [squash] { 'H; x: 'u *['g] 'v = 'u *['g] 'w in 'g^car; 'J['x] >- 'g in group[i:l] } -->
   sequent [squash] { 'H; x: 'u *['g] 'v = 'u *['g] 'w in 'g^car; 'J['x] >- 'u in 'g^car } -->
   sequent [squash] { 'H; x: 'u *['g] 'v = 'u *['g] 'w in 'g^car; 'J['x] >- 'v in 'g^car } -->
   sequent [squash] { 'H; x: 'u *['g] 'v = 'u *['g] 'w in 'g^car; 'J['x] >- 'w in 'g^car } -->
   sequent ['ext] { 'H; x: 'u *['g] 'v = 'u *['g] 'w in 'g^car; 'J['x] >- 'v = 'w in 'g^car }

(* Cancellation: b * a = c * a => b = c *)
interactive cancel_right {| elim [elim_typeinf <<'g>>] |} 'H 'J group[i:l] :
   sequent [squash] { 'H; x: 'v *['g] 'u = 'w *['g] 'u in 'g^car; 'J['x] >- 'g in group[i:l] } -->
   sequent [squash] { 'H; x: 'v *['g] 'u = 'w *['g] 'u in 'g^car; 'J['x] >- 'u in 'g^car } -->
   sequent [squash] { 'H; x: 'v *['g] 'u = 'w *['g] 'u in 'g^car; 'J['x] >- 'v in 'g^car } -->
   sequent [squash] { 'H; x: 'v *['g] 'u = 'w *['g] 'u in 'g^car; 'J['x] >- 'w in 'g^car } -->
   sequent ['ext] { 'H; x: 'v *['g] 'u = 'w *['g] 'u in 'g^car; 'J['x] >- 'v = 'w in 'g^car }

(*!
 * @begin[doc]
 *
 * Unique identity (left and right).
 * @end[doc]
 *)
interactive unique_id_left 'H group[i:l] :
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'e2 in 'g^car } -->
   [main] sequent ['ext] {'H >- all a: 'g^car. 'e2 *['g] 'a = 'a in 'g^car } -->
   sequent ['ext] {'H >- 'e2 = 'g^"1" in 'g^car }

interactive unique_id_right 'H group[i:l] :
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'e2 in 'g^car } -->
   [main] sequent ['ext] {'H >- all a: 'g^car. 'a *['g] 'e2 = 'a in 'g^car } -->
   sequent ['ext] {'H >- 'e2 = 'g^"1" in 'g^car }

(*!
 * @begin[doc]
 *
 * Unique inverse (left and right).
 * @end[doc]
 *)
interactive unique_inv_left {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'a in 'g^car } -->
   [wf] sequent [squash] {'H >- 'a2 in 'g^car } -->
   [main] sequent ['ext] {'H >- 'a2 *['g] 'a = 'g^"1" in 'g^car } -->
   sequent ['ext] {'H >- 'a2 = 'g^inv 'a in 'g^car }

interactive unique_inv_right {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'a in 'g^car } -->
   [wf] sequent [squash] {'H >- 'a2 in 'g^car } -->
   [main] sequent ['ext] {'H >- 'a *['g] 'a2 = 'g^"1" in 'g^car } -->
   sequent ['ext] {'H >- 'a2 = 'g^inv 'a in 'g^car }

(*!
 * @begin[doc]
 *
 * Unique solution.
 * @end[doc]
 *)
(* The unique solution for a * x = b is x = a' * b *)
interactive unique_sol1 {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'a in 'g^car } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   [wf] sequent [squash] {'H >- 'x in 'g^car } -->
   [main] sequent ['ext] {'H >- 'a *['g] 'x = 'b in 'g^car } -->
   sequent ['ext] {'H >- 'x = ('g^inv 'a) *['g] 'b in 'g^car }

(* The unique solution for y * a = b is y = b * a' *)
interactive unique_sol2 {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'a in 'g^car } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   [wf] sequent [squash] {'H >- 'y in 'g^car } -->
   [main] sequent ['ext] {'H >- 'y *['g] 'a = 'b in 'g^car } -->
   sequent ['ext] {'H >- 'y = 'b *['g] ('g^inv 'a) in 'g^car }

(*!
 * @begin[doc]
 *
 * Inverse simplification.
 * @end[doc]
 *)
(* (a * b)' = b' * a'  *)
interactive inv_simplify {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent [squash] {'H >- 'b in 'g^car } -->
   sequent ['ext] {'H >- 'g^inv ('a *['g] 'b)  = ('g^inv 'b) *['g] ('g^inv 'a) in 'g^car }
(*! @docoff *)

(* Inverse of id *)
interactive inv_of_id {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- 'g^inv 'g^"1" = 'g^"1" in 'g^car }

(* e * a = a * e *)
interactive id_commut1 {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- 'g^"1" *['g] 'a = 'a *['g] 'g^"1" in 'g^car }

(* a * e = e * a *)
interactive id_commut2 {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- 'a *['g] 'g^"1" = 'g^"1" *['g] 'a in 'g^car }

(*!
 * @begin[doc]
 * @modsubsection{Abelian group}
 *
 * @end[doc]
 *)
interactive abelg_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{abelg[i:l]} }

interactive abelg_intro {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- isCommutative{'g} } -->
   sequent ['ext] { 'H >- 'g in abelg[i:l] }

interactive abelg_elim {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; g: group[i:l]; x: isCommutative{'g}; 'J['g] >- 'C['g] } -->
   sequent ['ext] { 'H; g: abelg[i:l]; 'J['g] >- 'C['g] }
(*! @docoff *)

interactive subgroup_ref {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- subStructure{'g; 'g} }

(*!
 * @begin[doc]
 * @modsubsection{Subgroup}
 *
 * If $s$ is a subgroup of $g$, then
 * @begin[enumerate]
 * @item{$s$ is closed under the binary operation of $g$.}
 * @item{the identity of $s$ is the identity of $g$.}
 * @item{the inverse of $a @in @car{s}$ is also the inverse of $a$ in $g$.}
 * @end[enumerate]
 * @end[doc]
 *)
interactive subgroup_op {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'a in 's^car } -->
   [wf] sequent [squash] {'H >- 'b in 's^car } -->
   sequent ['ext] { 'H >- 'a *['g] 'b in 's^car }

interactive subgroup_id {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   sequent ['ext] {'H >- 's^"1" = 'g^"1" in 's^car }

interactive subgroup_inv {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'a in 's^car } -->
   sequent ['ext] {'H >- 's^inv 'a = 'g^inv 'a in 's^car }

(*!
 * @begin[doc]
 *
 * A non-empty subset $S$ is a subgroup of $G$ only if
 * for all $a, b @in H$, $@mul{g; a; @inv{g; b}} @in @car{h}$
 * @end[doc]
 *)
interactive subgroup_thm1 'H group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   sequent ['ext] { 'H >- all a: 's^car. all b: 's^car. ('a *['g] ('g^inv 'b) in 's^car) }

(*!
 * @begin[doc]
 *
 * The intersection group of subgroups $h_1$ and $h_2$ of
 * a group $g$ is again a subgroup of $g$.
 * @end[doc]
 *)
interactive subgroup_isect 'H 's1 's2 group[i:l] :
   sequent [squash] {'H >- 's1 in group[i:l] } -->
   sequent [squash] {'H >- 's2 in group[i:l] } -->
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 's in group[i:l] } -->
   sequent ['ext] { 'H >- subStructure{'s1; 'g} } -->
   sequent ['ext] { 'H >- subStructure{'s2; 'g} } -->
   sequent ['ext] { 'H >- 's^car = "isect"{.'s1^car; x. 's2^car} in univ[i:l] } -->
   sequent ['ext] { 'H >- 's^"*" = 's1^"*" in 's^car -> 's^car -> 's^car } -->
   sequent ['ext] { 'H >- subStructure{'s; 'g} }

(*!
 * @begin[doc]
 * @modsubsection{Coset}
 *
 * @end[doc]
 *)
interactive lcoset_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{.'g^car} } -->
   [wf] sequent [squash] { 'H >- "type"{.'s^car} } -->
   [wf] sequent [squash] { 'H; a: 's^car >- 'b *['g] 'a in 'g^car } -->
   sequent ['ext] { 'H >- "type"{lcoset{'s; 'g; 'b}} }

interactive rcoset_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{.'g^car} } -->
   [wf] sequent [squash] { 'H >- "type"{.'s^car} } -->
   [wf] sequent [squash] { 'H; a: 's^car >- 'a *['g] 'b in 'g^car } -->
   sequent ['ext] { 'H >- "type"{rcoset{'s; 'g; 'b}} }

interactive lcoset_intro {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] 'x :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   [wf] sequent [squash] {'H >- 'x in 'g^car } -->
   [main] sequent [squash] {'H >- exst a: 's^car. 'x = 'b *['g] 'a in 'g^car } -->
   sequent ['ext] { 'H >- lcoset{'s; 'g; 'b} }

interactive rcoset_intro {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] 'x :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   [wf] sequent [squash] {'H >- 'x in 'g^car } -->
   [main] sequent [squash] {'H >- exst a: 's^car. 'x = 'a *['g] 'b in 'g^car } -->
   sequent ['ext] { 'H >- rcoset{'s; 'g; 'b} }

interactive lcoset_member_intro {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] 'a :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   [wf] sequent [squash] {'H >- 'x1 = 'x2 in 'g^car } -->
   [wf] sequent [squash] {'H >- 'a in 's^car } -->
   [main] sequent [squash] {'H >- 'x1 = 'b *['g] 'a in 'g^car } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in lcoset{'s; 'g; 'b} }

interactive rcoset_member_intro {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] 'a :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [wf] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   [wf] sequent [squash] {'H >- 'x1 = 'x2 in 'g^car } -->
   [wf] sequent [squash] {'H >- 'a in 's^car } -->
   [main] sequent ['ext] {'H >- 'x1 = 'a *['g] 'b in 'g^car } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in rcoset{'s; 'g; 'b} }

interactive lcoset_elim {| elim [elim_typeinf <<'g>>] |} 'H 'J group[i:l] :
   [wf] sequent [squash] {'H; u: lcoset{'s; 'g; 'b}; 'J['u] >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H; u: lcoset{'s; 'g; 'b}; 'J['u] >- 'g in group[i:l] } -->
   [wf] sequent ['ext] { 'H; u: lcoset{'s; 'g; 'b}; 'J['u] >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H; u: lcoset{'s; 'g; 'b}; 'J['u] >- 'b in 'g^car } -->
   [main] sequent ['ext] {'H; u: 'g^car; v: squash{.exst a: 's^car. 'u = 'b *['g] 'a in 'g^car}; 'J['u] >- 'C['u] } -->
   sequent ['ext] { 'H; u: lcoset{'s; 'g; 'b}; 'J['u] >- 'C['u] }

interactive rcoset_elim {| elim [elim_typeinf <<'g>>] |} 'H 'J group[i:l] :
   [wf] sequent [squash] {'H; u: rcoset{'s; 'g; 'b}; 'J['u] >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H; u: rcoset{'s; 'g; 'b}; 'J['u] >- 'g in group[i:l] } -->
   [wf] sequent ['ext] { 'H; u: rcoset{'s; 'g; 'b}; 'J['u] >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H; u: rcoset{'s; 'g; 'b}; 'J['u] >- 'b in 'g^car } -->
   [main] sequent ['ext] {'H; u: 'g^car; v: squash{.exst a: 's^car. 'u = 'a *['g] 'b in 'g^car}; 'J['u] >- 'C['u] } -->
   sequent ['ext] { 'H; u: rcoset{'s; 'g; 'b}; 'J['u] >- 'C['u] }

(*!
 * @begin[doc]
 *
 * If $s$ is a subgroup of group $g$, both the left and right
 * cosets of $s$ containing $b$ are subsets of the carrier of
 * $g$.
 * @end[doc]
 *)
interactive lcoset_subset {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   sequent ['ext] { 'H >- \subset{lcoset{'s; 'g; 'b}; .'g^car} }

interactive rcoset_subset {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H >- 'b in 'g^car } -->
   sequent ['ext] { 'H >- \subset{rcoset{'s; 'g; 'b}; .'g^car} }

(*!
 * @begin[doc]
 * @modsubsection{Normal subgroup}
 *
 * @end[doc]
 *)
(*
interactive normalSubg_wf {| intro [] |} 'H :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   sequent ['ext] { 'H >- "type"{normalSubg[i:l]{'s; 'g}} }
*)

interactive normalSubg_intro {| intro [] |} 'H :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   [main] sequent ['ext] { 'H; x: 'g^car >- lcoset{'s; 'g; 'x} = rcoset{'s; 'g; 'x} in univ[i:l] } -->
   sequent ['ext] { 'H >- normalSubg[i:l]{'s; 'g} }

interactive normalSubg_elim {| elim [] |} 'H 'J 'y 'b :
   [wf] sequent [squash] {'H; x: normalSubg[i:l]{'s; 'g}; 'J['x] >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H; x: normalSubg[i:l]{'s; 'g}; 'J['x] >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H; x: normalSubg[i:l]{'s; 'g}; 'J['x] >- subStructure{'s; 'g} } -->
   [wf] sequent [squash] {'H; x: normalSubg[i:l]{'s; 'g}; 'J['x] >- 'b in 'g^car } -->
   [main] sequent ['ext] { 'H; x: normalSubg[i:l]{'s; 'g}; 'J['x]; y: lcoset{'s; 'g; 'b} = rcoset{'s; 'g; 'b} in univ[i:l] >- 'C['x] } -->
   sequent ['ext] { 'H; x: normalSubg[i:l]{'s; 'g}; 'J['x] >- 'C['x] }

(*!
 * @begin[doc]
 *
 * All subgroups of abelian groups are normal.
 * @end[doc]
 *)
interactive abel_subg_normal 'H :
   [wf] sequent [squash] {'H >- 's in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'g in group[i:l] } -->
   [main] sequent ['ext] { 'H >- isCommutative{'g} } -->
   [main] sequent ['ext] { 'H >- subStructure{'s; 'g} } -->
   sequent ['ext] { 'H >- normalSubg[i:l]{'s; 'g} }

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Group Homomorphism}
 *
 * @end[doc]
 *)
interactive groupHom_type {| intro [intro_typeinf <<'G>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H >- 'G in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'H in group[i:l] } -->
    sequent ['ext] { 'H >- "type"{groupHom{'G; 'H}} }

interactive groupHom_intro {| intro [intro_typeinf <<'G>>] |} 'H group[i:l] :
   [wf] sequent [squash] {'H >- 'G in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'H in group[i:l] } -->
   [wf] sequent [squash] {'H >- 'f in 'G^car -> 'H^car } -->
   [main] sequent ['ext] { 'H; x: 'G^car; y: 'G^car >- ('f ('x *['G] 'y)) = ('f 'x) *['H] ('f 'y) in 'H^car } -->
    sequent ['ext] { 'H >- 'f in groupHom{'G; 'H} }

interactive groupHom_elim {| elim [elim_typeinf <<'G>>] |} 'H 'J group[i:l] :
   [wf] sequent [squash] {'H; f: groupHom{'G; 'H}; 'J['f] >- 'G in group[i:l] } -->
   [wf] sequent [squash] {'H; f: groupHom{'G; 'H}; 'J['f] >- 'H in group[i:l] } -->
   [main] sequent ['ext] { 'H; f: 'G^car -> 'H^car; u: all x: 'G^car. all y: 'G^car. ('f ('x *['G] 'y)) = ('f 'x) *['H] ('f 'y) in 'H^car; 'J['f] >- 'C['f] } -->
   sequent ['ext] { 'H; f: groupHom{'G; 'H}; 'J['f] >- 'C['f] }   
(*! @docoff *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
