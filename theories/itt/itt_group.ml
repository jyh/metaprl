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
open Itt_grouplikeobj

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
   record["inv":t]{r. 'r^"G" -> 'r^"G"; premonoid[i:l]}

define unfold_isGroup : isGroup{'g} <-->
   isSemigroup{'g} & all x: 'g^"G". ('g^"*") ('g^"e") 'x = 'x in 'g^"G" & all x: 'g^"G". ('g^"*") (('g^"inv") 'x) 'x = ('g^"e") in 'g^"G"

define unfold_group1 : group[i:l] <-->
   {g: pregroup[i:l] | isGroup{'g}}

define unfold_abelg1 : abelg[i:l] <-->
   {g: pregroup[i:l] | isGroup{'g} & isCommutative{'g}}
(*! @docoff *)

interactive_rw unfold_pregroup :
   pregroup[i:l] <--> record["inv":t]{r. 'r^"G" -> 'r^"G"; record["e":t]{r. 'r^"G"; {"G": univ[i:l]; "*": ^"G" -> ^"G" -> ^"G"}}}

interactive_rw unfold_group :
   group[i:l] <--> {self: {"G": univ[i:l]; "*": ^"G" -> ^"G" -> ^"G"; "e": ^"G"; "inv": ^"G" -> ^"G"} | (all x: ^"G". all y: ^"G". all z: ^"G". ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^"G") & (all x: ^"G". ^"e" ^* 'x = 'x in ^"G") & (all x: ^"G". ((^"inv") 'x) ^* 'x = ^"e" in ^"G")}

interactive_rw unfold_abelg :
   abelg[i:l] <--> {self: {"G": univ[i:l]; "*": ^"G" -> ^"G" -> ^"G"; "e": ^"G"; "inv": ^"G" -> ^"G"} | ((all x: ^"G". all y: ^"G". all z: ^"G". ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^"G") & (all x: ^"G". ^"e" ^* 'x = 'x in ^"G") & (all x: ^"G". ((^"inv") 'x) ^* 'x = ^"e" in ^"G")) & (all x: ^"G". all y: ^"G". 'x ^* 'y = 'y ^* 'x in ^"G")}

let fold_pregroup1 = makeFoldC << pregroup[i:l] >> unfold_pregroup1
let fold_pregroup = makeFoldC << pregroup[i:l] >> unfold_pregroup
let fold_isGroup = makeFoldC << isGroup{'g} >> unfold_isGroup
let fold_group1 = makeFoldC << group[i:l] >> unfold_group1
let fold_group = makeFoldC << group[i:l] >> unfold_group
let fold_abelg1 = makeFoldC << abelg[i:l] >> unfold_abelg1
let fold_abelg = makeFoldC << abelg[i:l] >> unfold_abelg

let groupDT n = rw unfold_group n thenT dT n
let abelgDT n = rw unfold_abelg n thenT dT n

let resource elim +=
   [<<group[i:l]>>, groupDT;
    <<abelg[i:l]>>, abelgDT
   ]

let resource intro +=
   [<<group[i:l]>>, wrap_intro (groupDT 0);
    <<abelg[i:l]>>, wrap_intro (abelgDT 0)
   ]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform group_df : except_mode[src] :: group[i:l] =
   `"Group[" slot[i:l] `"]"

dform pregroup_df : except_mode[src] :: pregroup[i:l] =
   `"pregroup[" slot[i:l] `"]"

dform isGroup_df : except_mode[src] :: isGroup{'g} =
   `"isGroup(" slot{'g} `")"

dform abelg_df : except_mode[src] :: abelg[i:l] =
   `"Abelian Group[" slot[i:l] `"]"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Well-formedness}
 *
 * The @tt{group} is well-formed.
 * @end[doc]
 *)
interactive group_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{group[i:l]} }

interactive group_elim {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; g: {"G": univ[i:l]; "*": ^"G" -> ^"G" -> ^"G"; "e": ^"G"; "inv": ^"G" -> ^"G"}; u: squash{.all x: 'g^"G". all y: 'g^"G". all z: 'g^"G". (('g^"*") (('g^"*") 'x 'y) 'z = ('g^"*") 'x (('g^"*") 'y 'z) in 'g^"G")}; v: squash{.all x: 'g^"G". ('g^"*") ('g^"e") 'x = 'x in 'g^"G"}; w: squash{.all x: 'g^"G". ('g^"*") (('g^"inv") 'x) 'x = ('g^"e") in 'g^"G"}; 'J['g] >- 'C['g] } -->
   sequent ['ext] { 'H; g: group[i:l]; 'J['g] >- 'C['g] }   

interactive op_wf {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- ('g^"*") in ('g^"G") -> ('g^"G") -> ('g^"G") }

interactive inv_wf {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- ('g^"inv") in ('g^"G") -> ('g^"G") }

interactive op_in_G {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent [squash] {'H >- 'b in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"*") 'a 'b in 'g^"G" }

interactive id_in_G {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- 'g^"e" in 'g^"G" }

interactive inv_in_G {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"inv") 'a in 'g^"G" }

interactive group_assoc {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent [squash] {'H >- 'b in 'g^"G" } -->
   sequent [squash] {'H >- 'c in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"*") (('g^"*") 'a 'b) 'c = ('g^"*") 'a (('g^"*") 'b 'c) in 'g^"G" }

interactive group_left_id {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"*") ('g^"e") 'a = 'a in 'g^"G" }

interactive group_left_inv {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"*") (('g^"inv") 'a) 'a = ('g^"e") in 'g^"G" }

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
   sequent [squash] {'H; x: ('g^"*") 'u 'u = 'u in 'g^"G"; 'J['x] >- 'g in group[i:l] } -->
   sequent ['ext] {'H; x: ('g^"*") 'u 'u = 'u in 'g^"G"; 'J['x]; y: 'u = 'g^"e" in 'g^"G" >- 'C['x] } -->
   sequent ['ext] {'H; x: ('g^"*") 'u 'u = 'u in 'g^"G"; 'J['x] >- 'C['x] }

interactive right_inv {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"*") 'a (('g^"inv") 'a) = ('g^"e") in 'g^"G" }

interactive right_id {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"*") 'a ('g^"e") = 'a in 'g^"G" }

(*!
 * @begin[doc]
 * @modsubsection{Theorems}
 *
 * A group is also a monoid.
 * @end[doc]
 *)
interactive group_is_monoid {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g in group[i:l] } -->
   sequent ['ext] { 'H >- 'g in monoid[i:l] }

(*!
 * @begin[doc]
 * @modsubsection{Theorems}
 *
 * $@space @space$
 *
 * The left and right cancellation laws.
 * @end[doc]
 *)
(* Cancellation: a * b = a * c => b = c *)
interactive cancel_left {| elim [elim_typeinf <<'g>>] |} 'H 'J group[i:l] :
   sequent [squash] { 'H; x: ('g^"*") 'u 'v = ('g^"*") 'u 'w in 'g^"G"; 'J['x] >- 'g in group[i:l] } -->
   sequent [squash] { 'H; x: ('g^"*") 'u 'v = ('g^"*") 'u 'w in 'g^"G"; 'J['x] >- 'u in 'g^"G" } -->
   sequent [squash] { 'H; x: ('g^"*") 'u 'v = ('g^"*") 'u 'w in 'g^"G"; 'J['x] >- 'v in 'g^"G" } -->
   sequent [squash] { 'H; x: ('g^"*") 'u 'v = ('g^"*") 'u 'w in 'g^"G"; 'J['x] >- 'w in 'g^"G" } -->
   sequent ['ext] { 'H; x: ('g^"*") 'u 'v = ('g^"*") 'u 'w in 'g^"G"; 'J['x] >- 'v = 'w in 'g^"G" }

(* Cancellation: b * a = c * a => b = c *)
interactive cancel_right {| elim [elim_typeinf <<'g>>] |} 'H 'J group[i:l] :
   sequent [squash] { 'H; x: ('g^"*") 'v 'u = ('g^"*") 'w 'u in 'g^"G"; 'J['x] >- 'g in group[i:l] } -->
   sequent [squash] { 'H; x: ('g^"*") 'v 'u = ('g^"*") 'w 'u in 'g^"G"; 'J['x] >- 'u in 'g^"G" } -->
   sequent [squash] { 'H; x: ('g^"*") 'v 'u = ('g^"*") 'w 'u in 'g^"G"; 'J['x] >- 'v in 'g^"G" } -->
   sequent [squash] { 'H; x: ('g^"*") 'v 'u = ('g^"*") 'w 'u in 'g^"G"; 'J['x] >- 'w in 'g^"G" } -->
   sequent ['ext] { 'H; x: ('g^"*") 'v 'u = ('g^"*") 'w 'u in 'g^"G"; 'J['x] >- 'v = 'w in 'g^"G" }

(*!
 * @begin[doc]
 *
 * Unique identity (left and right).
 * @end[doc]
 *)
interactive unique_id_left 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'e2 in 'g^"G" } -->
   sequent ['ext] {'H >- all a: 'g^"G". ('g^"*") 'e2 'a = 'a in 'g^"G" } -->
   sequent ['ext] {'H >- 'e2 = ('g^"e") in 'g^"G" }

interactive unique_id_right 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'e2 in 'g^"G" } -->
   sequent ['ext] {'H >- all a: 'g^"G". ('g^"*") 'a 'e2 = 'a in 'g^"G" } -->
   sequent ['ext] {'H >- 'e2 = ('g^"e") in 'g^"G" }

(*!
 * @begin[doc]
 *
 * Unique inverse (left and right).
 * @end[doc]
 *)
interactive unique_inv_left {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent [squash] {'H >- 'a2 in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"*") 'a2 'a = ('g^"e") in 'g^"G" } -->
   sequent ['ext] {'H >- 'a2 = ('g^"inv") 'a in 'g^"G" }

interactive unique_inv_right {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent [squash] {'H >- 'a2 in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"*") 'a 'a2 = ('g^"e") in 'g^"G" } -->
   sequent ['ext] {'H >- 'a2 = ('g^"inv") 'a in 'g^"G" }

(*!
 * @begin[doc]
 *
 * Unique solution.
 * @end[doc]
 *)
(* The unique solution for a * x = b is x = a' * b *)
interactive unique_sol1 {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent [squash] {'H >- 'b in 'g^"G" } -->
   sequent [squash] {'H >- 'x in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"*") 'a 'x = 'b in 'g^"G" } -->
   sequent ['ext] {'H >- 'x = ('g^"*") (('g^"inv") 'a) 'b in 'g^"G" }

(* The unique solution for y * a = b is y = b * a' *)
interactive unique_sol2 {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent [squash] {'H >- 'b in 'g^"G" } -->
   sequent [squash] {'H >- 'y in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"*") 'y 'a = 'b in 'g^"G" } -->
   sequent ['ext] {'H >- 'y = ('g^"*") 'b (('g^"inv") 'a) in 'g^"G" }

(*!
 * @begin[doc]
 *
 * Inverse simplification. 
 * @end[doc]
 *)
(* (a * b)' = b' * a'  *)
interactive inv_simplify {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent [squash] {'H >- 'b in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"inv") (('g^"*") 'a 'b)  = ('g^"*") (('g^"inv") 'b) (('g^"inv") 'a) in 'g^"G" }
(*! @docoff *)

(* Inverse of id *)
interactive inv_of_id {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- ('g^"inv") ('g^"e") = ('g^"e") in 'g^"G" }

(* e * a = a * e *)
interactive id_commut1 {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"*") ('g^"e") 'a = ('g^"*") 'a ('g^"e") in 'g^"G" }

(* a * e = e * a *)
interactive id_commut2 {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^"G" } -->
   sequent ['ext] {'H >- ('g^"*") 'a ('g^"e") = ('g^"*") ('g^"e") 'a in 'g^"G" }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
