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
   record["inv":t]{r. 'r^car -> 'r^car; premonoid[i:l]}

define unfold_isGroup : isGroup{'g} <-->
   isSemigroup{'g} & all x: 'g^car. ('g^"*") ('g^"1") 'x = 'x in 'g^car & all x: 'g^car. ('g^"*") (('g^inv) 'x) 'x = ('g^"1") in 'g^car

define unfold_group1 : group[i:l] <-->
   {g: pregroup[i:l] | isGroup{'g}}

define unfold_abelg1 : abelg[i:l] <-->
   {g: pregroup[i:l] | isGroup{'g} & isCommutative{'g}}
(*! @docoff *)

interactive_rw unfold_pregroup :
   pregroup[i:l] <--> {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car}

interactive_rw unfold_group :
   group[i:l] <--> {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car; (all x: ^car. all y: ^car. all z: ^car. ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^car) & (all x: ^car. ^"1" ^* 'x = 'x in ^car) & (all x: ^car. ((^inv) 'x) ^* 'x = ^"1" in ^car)}

interactive_rw unfold_abelg :
   abelg[i:l] <--> {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car; ((all x: ^car. all y: ^car. all z: ^car. ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^car) & (all x: ^car. ^"1" ^* 'x = 'x in ^car) & (all x: ^car. ((^inv) 'x) ^* 'x = ^"1" in ^car)) & (all x: ^car. all y: ^car. 'x ^* 'y = 'y ^* 'x in ^car)}

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
   sequent ['ext] { 'H; g: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car}; u: squash{.all x: 'g^car. all y: 'g^car. all z: 'g^car. (('g^"*") (('g^"*") 'x 'y) 'z = ('g^"*") 'x (('g^"*") 'y 'z) in 'g^car)}; v: squash{.all x: 'g^car. ('g^"*") ('g^"1") 'x = 'x in 'g^car}; w: squash{.all x: 'g^car. ('g^"*") (('g^inv) 'x) 'x = ('g^"1") in 'g^car}; 'J['g] >- 'C['g] } -->
   sequent ['ext] { 'H; g: group[i:l]; 'J['g] >- 'C['g] }   

interactive op_wf {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- ('g^"*") in ('g^car) -> ('g^car) -> ('g^car) }

interactive inv_wf {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- ('g^inv) in ('g^car) -> ('g^car) }

interactive op_in_G {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent [squash] {'H >- 'b in 'g^car } -->
   sequent ['ext] {'H >- ('g^"*") 'a 'b in 'g^car }

interactive id_in_G {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- 'g^"1" in 'g^car }

interactive inv_in_G {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- ('g^inv) 'a in 'g^car }

interactive group_assoc {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent [squash] {'H >- 'b in 'g^car } -->
   sequent [squash] {'H >- 'c in 'g^car } -->
   sequent ['ext] {'H >- ('g^"*") (('g^"*") 'a 'b) 'c = ('g^"*") 'a (('g^"*") 'b 'c) in 'g^car }

interactive group_left_id {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- ('g^"*") ('g^"1") 'a = 'a in 'g^car }

interactive group_left_inv {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- ('g^"*") (('g^inv) 'a) 'a = ('g^"1") in 'g^car }

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
   sequent [squash] {'H; x: ('g^"*") 'u 'u = 'u in 'g^car; 'J['x] >- 'g in group[i:l] } -->
   sequent ['ext] {'H; x: ('g^"*") 'u 'u = 'u in 'g^car; 'J['x]; y: 'u = 'g^"1" in 'g^car >- 'C['x] } -->
   sequent ['ext] {'H; x: ('g^"*") 'u 'u = 'u in 'g^car; 'J['x] >- 'C['x] }

interactive right_inv {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- ('g^"*") 'a (('g^inv) 'a) = ('g^"1") in 'g^car }

interactive right_id {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- ('g^"*") 'a ('g^"1") = 'a in 'g^car }

(*!
 * @begin[doc]
 * @modsubsection{Theorems}
 *
 * A group is also a monoid.
 * @end[doc]
 *)
interactive group_is_monoid 'H :
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
   sequent [squash] { 'H; x: ('g^"*") 'u 'v = ('g^"*") 'u 'w in 'g^car; 'J['x] >- 'g in group[i:l] } -->
   sequent [squash] { 'H; x: ('g^"*") 'u 'v = ('g^"*") 'u 'w in 'g^car; 'J['x] >- 'u in 'g^car } -->
   sequent [squash] { 'H; x: ('g^"*") 'u 'v = ('g^"*") 'u 'w in 'g^car; 'J['x] >- 'v in 'g^car } -->
   sequent [squash] { 'H; x: ('g^"*") 'u 'v = ('g^"*") 'u 'w in 'g^car; 'J['x] >- 'w in 'g^car } -->
   sequent ['ext] { 'H; x: ('g^"*") 'u 'v = ('g^"*") 'u 'w in 'g^car; 'J['x] >- 'v = 'w in 'g^car }

(* Cancellation: b * a = c * a => b = c *)
interactive cancel_right {| elim [elim_typeinf <<'g>>] |} 'H 'J group[i:l] :
   sequent [squash] { 'H; x: ('g^"*") 'v 'u = ('g^"*") 'w 'u in 'g^car; 'J['x] >- 'g in group[i:l] } -->
   sequent [squash] { 'H; x: ('g^"*") 'v 'u = ('g^"*") 'w 'u in 'g^car; 'J['x] >- 'u in 'g^car } -->
   sequent [squash] { 'H; x: ('g^"*") 'v 'u = ('g^"*") 'w 'u in 'g^car; 'J['x] >- 'v in 'g^car } -->
   sequent [squash] { 'H; x: ('g^"*") 'v 'u = ('g^"*") 'w 'u in 'g^car; 'J['x] >- 'w in 'g^car } -->
   sequent ['ext] { 'H; x: ('g^"*") 'v 'u = ('g^"*") 'w 'u in 'g^car; 'J['x] >- 'v = 'w in 'g^car }

(*!
 * @begin[doc]
 *
 * Unique identity (left and right).
 * @end[doc]
 *)
interactive unique_id_left 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'e2 in 'g^car } -->
   sequent ['ext] {'H >- all a: 'g^car. ('g^"*") 'e2 'a = 'a in 'g^car } -->
   sequent ['ext] {'H >- 'e2 = ('g^"1") in 'g^car }

interactive unique_id_right 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'e2 in 'g^car } -->
   sequent ['ext] {'H >- all a: 'g^car. ('g^"*") 'a 'e2 = 'a in 'g^car } -->
   sequent ['ext] {'H >- 'e2 = ('g^"1") in 'g^car }

(*!
 * @begin[doc]
 *
 * Unique inverse (left and right).
 * @end[doc]
 *)
interactive unique_inv_left {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent [squash] {'H >- 'a2 in 'g^car } -->
   sequent ['ext] {'H >- ('g^"*") 'a2 'a = ('g^"1") in 'g^car } -->
   sequent ['ext] {'H >- 'a2 = ('g^inv) 'a in 'g^car }

interactive unique_inv_right {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent [squash] {'H >- 'a2 in 'g^car } -->
   sequent ['ext] {'H >- ('g^"*") 'a 'a2 = ('g^"1") in 'g^car } -->
   sequent ['ext] {'H >- 'a2 = ('g^inv) 'a in 'g^car }

(*!
 * @begin[doc]
 *
 * Unique solution.
 * @end[doc]
 *)
(* The unique solution for a * x = b is x = a' * b *)
interactive unique_sol1 {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent [squash] {'H >- 'b in 'g^car } -->
   sequent [squash] {'H >- 'x in 'g^car } -->
   sequent ['ext] {'H >- ('g^"*") 'a 'x = 'b in 'g^car } -->
   sequent ['ext] {'H >- 'x = ('g^"*") (('g^inv) 'a) 'b in 'g^car }

(* The unique solution for y * a = b is y = b * a' *)
interactive unique_sol2 {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent [squash] {'H >- 'b in 'g^car } -->
   sequent [squash] {'H >- 'y in 'g^car } -->
   sequent ['ext] {'H >- ('g^"*") 'y 'a = 'b in 'g^car } -->
   sequent ['ext] {'H >- 'y = ('g^"*") 'b (('g^inv) 'a) in 'g^car }

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
   sequent ['ext] {'H >- ('g^inv) (('g^"*") 'a 'b)  = ('g^"*") (('g^inv) 'b) (('g^inv) 'a) in 'g^car }
(*! @docoff *)

(* Inverse of id *)
interactive inv_of_id {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent ['ext] {'H >- ('g^inv) ('g^"1") = ('g^"1") in 'g^car }

(* e * a = a * e *)
interactive id_commut1 {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- ('g^"*") ('g^"1") 'a = ('g^"*") 'a ('g^"1") in 'g^car }

(* a * e = e * a *)
interactive id_commut2 {| intro [intro_typeinf <<'g>>] |} 'H group[i:l] :
   sequent [squash] {'H >- 'g in group[i:l] } -->
   sequent [squash] {'H >- 'a in 'g^car } -->
   sequent ['ext] {'H >- ('g^"*") 'a ('g^"1") = ('g^"*") ('g^"1") 'a in 'g^car }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
