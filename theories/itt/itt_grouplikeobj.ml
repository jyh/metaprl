(*!
 * @spelling{groupoid semigroup monoid}
 *
 * @begin[doc]
 * @module[Itt_grouplikeobj]
 *
 * This theory defines group-like objects: groupoid, semigroup, and monoid.
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
extends Itt_record
(*! @docoff *)
extends Itt_set
extends Itt_fun
extends Itt_disect

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
open Itt_logic

let _ =
   show_loading "Loading Itt_grouplikeobj%t"

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * @end[doc]
 *)
define unfold_groupoid : groupoid[i:l] <-->
   {"G": univ[i:l]; "*": ^"G" -> ^"G" -> ^"G"}

define unfold_isSemigroup : isSemigroup{'g} <-->
   all x: 'g^"G". all y: 'g^"G". all z: 'g^"G". (('g^"*") (('g^"*") 'x 'y) 'z = ('g^"*") 'x (('g^"*") 'y 'z) in 'g^"G")

define unfold_semigroup1 : semigroup[i:l] <-->
   {g: groupoid[i:l] | isSemigroup{'g}}

define unfold_premonoid : premonoid[i:l] <-->
   record["e":t]{r. 'r^"G"; groupoid[i:l]}

define unfold_isMonoid : isMonoid{'g} <-->
   isSemigroup{'g} & all x: 'g^"G". (('g^"*") ('g^"e") 'x = 'x  in 'g^"G" & ('g^"*") 'x ('g^"e") = 'x in 'g^"G" )

define unfold_monoid1 : monoid[i:l] <-->
   {g: premonoid[i:l] | isMonoid{'g}}
(*! @docoff *)

interactive_rw unfold_semigroup :
   semigroup[i:l] <--> {self: {"G": univ[i:l]; "*": ^"G" -> ^"G" -> ^"G"} | all x: ^"G". all y: ^"G". all z: ^"G". ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^"G"}

interactive_rw unfold_monoid :
   monoid[i:l] <--> {self: {"G": univ[i:l]; "*": ^"G" -> ^"G" -> ^"G"; "e": ^"G"} | (all x: ^"G". all y: ^"G". all z: ^"G". ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^"G") & (all x: ^"G". (^"e" ^* 'x = 'x in ^"G" & 'x ^* ^"e" = 'x in ^"G"))}

let groupoidDT n = rw unfold_groupoid n thenT dT n
let semigroupDT n = rw unfold_semigroup n thenT dT n
let monoidDT n = rw unfold_monoid n thenT dT n

let resource elim +=
   [<<groupoid[i:l]>>, groupoidDT;
    <<semigroup[i:l]>>, semigroupDT;
    <<monoid[i:l]>>, monoidDT
   ]

let resource intro +=
   [<<groupoid[i:l]>>, wrap_intro (groupoidDT 0);
    <<semigroup[i:l]>>, wrap_intro (semigroupDT 0);
    <<monoid[i:l]>>, wrap_intro (monoidDT 0)
   ]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform groupoid_df : except_mode[src] :: groupoid[i:l] =
   `"Groupoid[" slot[i:l] `"]"

dform semigroup_df : except_mode[src] :: semigroup[i:l] =
   `"Semigroup[" slot[i:l] `"]"

dform monoid_df : except_mode[src] :: monoid[i:l] =
   `"Monoid[" slot[i:l] `"]"

dform premonoid_df : except_mode[src] :: premonoid[i:l] =
   `"premonoid[" slot[i:l] `"]"

dform isMonoid_df : except_mode[src] :: isMonoid{'g} =
   `"isMonoid(" slot{'g} `")"

dform isSemigroup_df : except_mode[src] :: isSemigroup{'g} =
   `"isSemigroup(" slot{'g} `")"

interactive groupoid_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{groupoid[i:l]} }

interactive semigroup_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{semigroup[i:l]} }

interactive monoid_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{monoid[i:l]} }

interactive semigroup_elim {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; g: {"G": univ[i:l]; "*": ^"G" -> ^"G" -> ^"G"}; u: squash{.all x: 'g^"G". all y: 'g^"G". all z: 'g^"G". (('g^"*") (('g^"*") 'x 'y) 'z = ('g^"*") 'x (('g^"*") 'y 'z) in 'g^"G")}; 'J['g] >- 'C['g] } -->
   sequent ['ext] { 'H; g: semigroup[i:l]; 'J['g] >- 'C['g] }   

interactive monoid_elim {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; g: {"G": univ[i:l]; "*": ^"G" -> ^"G" -> ^"G"; "e": ^"G"}; u: squash{.all x: 'g^"G". all y: 'g^"G". all z: 'g^"G". (('g^"*") (('g^"*") 'x 'y) 'z = ('g^"*") 'x (('g^"*") 'y 'z) in 'g^"G")}; v: squash{.all x: 'g^"G". (('g^"*") ('g^"e") 'x = 'x in 'g^"G" & ('g^"*") 'x ('g^"e") = 'x in 'g^"G")}; 'J['g] >- 'C['g] } -->
   sequent ['ext] { 'H; g: monoid[i:l]; 'J['g] >- 'C['g] }   

interactive semigrp_is_grpoid2 'H :
   sequent ['ext] {'H; g: semigroup[i:l] >- 'g in groupoid[i:l] }

interactive semigrp_is_grpoid (*{| intro [] |}*) 'H :
   sequent [squash] { 'H >- 'h in semigroup[i:l] } -->
   sequent ['ext] { 'H >- 'h in groupoid[i:l] }

interactive monoid_is_semigrp (*{| intro [] |}*) 'H :
   sequent [squash] { 'H >- 'g in monoid[i:l] } -->
   sequent ['ext] { 'H >- 'g in semigroup[i:l] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
