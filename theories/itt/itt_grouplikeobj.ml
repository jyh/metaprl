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
   {car: univ[i:l]; "*": ^car -> ^car -> ^car}

define unfold_isSemigroup : isSemigroup{'g} <-->
   all x: 'g^car. all y: 'g^car. all z: 'g^car. (('g^"*") (('g^"*") 'x 'y) 'z = ('g^"*") 'x (('g^"*") 'y 'z) in 'g^car)

define unfold_semigroup1 : semigroup[i:l] <-->
   {g: groupoid[i:l] | isSemigroup{'g}}

define unfold_premonoid1 : premonoid[i:l] <-->
   record["1":t]{r. 'r^car; groupoid[i:l]}

define unfold_isMonoid : isMonoid{'g} <-->
   isSemigroup{'g} & all x: 'g^car. (('g^"*") ('g^"1") 'x = 'x  in 'g^car & ('g^"*") 'x ('g^"1") = 'x in 'g^car )

define unfold_monoid1 : monoid[i:l] <-->
   {g: premonoid[i:l] | isMonoid{'g}}

define unfold_isCommutative : isCommutative{'g} <-->
   all x: 'g^car. all y: 'g^car. (('g^"*") 'x 'y = ('g^"*") 'y 'x in 'g^car)

define unfold_csemigroup1 : csemigroup[i:l] <-->
   {g: groupoid[i:l] | isSemigroup{'g} & isCommutative{'g}}

define unfold_cmonoid1 : cmonoid[i:l] <-->
   {g: premonoid[i:l] | (isMonoid{'g}) & isCommutative{'g}}
(*! @docoff *)

interactive_rw unfold_semigroup :
   semigroup[i:l] <--> {car: univ[i:l]; "*": ^car -> ^car -> ^car; all x: ^car. all y: ^car. all z: ^car. ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^car}

interactive_rw unfold_premonoid : 
   premonoid[i:l] <--> record["1":t]{r. 'r^car; {car: univ[i:l]; "*": ^car -> ^car -> ^car}}

interactive_rw unfold_monoid :
   monoid[i:l] <--> {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; (all x: ^car. all y: ^car. all z: ^car. ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^car) & (all x: ^car. (^"1" ^* 'x = 'x in ^car & 'x ^* ^"1" = 'x in ^car))}

interactive_rw unfold_csemigroup :
   csemigroup[i:l] <--> {car: univ[i:l]; "*": ^car -> ^car -> ^car; (all x: ^car. all y: ^car. all z: ^car. ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^car) & (all x: ^car. all y: ^car. 'x ^* 'y = 'y ^* 'x in ^car)}

interactive_rw unfold_cmonoid :
   cmonoid[i:l] <--> {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; ((all x: ^car. all y: ^car. all z: ^car. ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^car) & (all x: ^car. (^"1" ^* 'x = 'x in ^car & 'x ^* ^"1" = 'x in ^car))) & (all x: ^car. all y: ^car. 'x ^* 'y = 'y ^* 'x in ^car)}

let fold_groupoid = makeFoldC << groupoid[i:l] >> unfold_groupoid
let fold_isSemigroup = makeFoldC << isSemigroup{'g} >> unfold_isSemigroup
let fold_semigroup1 = makeFoldC << semigroup[i:l] >> unfold_semigroup1
let fold_semigroup = makeFoldC << semigroup[i:l] >> unfold_semigroup
let fold_premonoid1 = makeFoldC << premonoid[i:l] >> unfold_premonoid1
let fold_premonoid = makeFoldC << premonoid[i:l] >> unfold_premonoid
let fold_isMonoid = makeFoldC << isMonoid{'g} >> unfold_isMonoid
let fold_monoid1 = makeFoldC << monoid[i:l] >> unfold_monoid1
let fold_monoid = makeFoldC << monoid[i:l] >> unfold_monoid
let fold_isCommutative = makeFoldC << isCommutative{'g} >> unfold_isCommutative
let fold_csemigroup1 = makeFoldC << csemigroup[i:l] >> unfold_csemigroup1
let fold_csemigroup = makeFoldC << csemigroup[i:l] >> unfold_csemigroup
let fold_cmonoid1 = makeFoldC << cmonoid[i:l] >> unfold_cmonoid1
let fold_cmonoid = makeFoldC << cmonoid[i:l] >> unfold_cmonoid

let groupoidDT n = rw unfold_groupoid n thenT dT n
let semigroupDT n = rw unfold_semigroup n thenT dT n
let monoidDT n = rw unfold_monoid n thenT dT n
let csemigroupDT n = rw unfold_csemigroup n thenT dT n
let cmonoidDT n = rw unfold_cmonoid n thenT dT n

let resource elim +=
   [<<groupoid[i:l]>>, groupoidDT;
    <<semigroup[i:l]>>, semigroupDT;
    <<monoid[i:l]>>, monoidDT;
    <<csemigroup[i:l]>>, csemigroupDT;
    <<cmonoid[i:l]>>, cmonoidDT
   ]

let resource intro +=
   [<<groupoid[i:l]>>, wrap_intro (groupoidDT 0);
    <<semigroup[i:l]>>, wrap_intro (semigroupDT 0);
    <<monoid[i:l]>>, wrap_intro (monoidDT 0);
    <<csemigroup[i:l]>>, wrap_intro (csemigroupDT 0);
    <<cmonoid[i:l]>>, wrap_intro (cmonoidDT 0)
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

dform isSemigroup_df : except_mode[src] :: isSemigroup{'g} =
   `"isSemigroup(" slot{'g} `")"

dform isMonoid_df : except_mode[src] :: isMonoid{'g} =
   `"isMonoid(" slot{'g} `")"

dform isCommutative_df : except_mode[src] :: isCommutative{'g} =
   `"isCommutative(" slot{'g} `")"

dform csemigroup_df : except_mode[src] :: csemigroup[i:l] =
   `"Commutative Semigroup[" slot[i:l] `"]"

dform cmonoid_df : except_mode[src] :: cmonoid[i:l] =
   `"Commutative Monoid[" slot[i:l] `"]"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive groupoid_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{groupoid[i:l]} }

interactive semigroup_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{semigroup[i:l]} }

interactive monoid_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{monoid[i:l]} }

interactive semigroup_elim {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; g: {car: univ[i:l]; "*": ^car -> ^car -> ^car}; u: squash{.all x: 'g^car. all y: 'g^car. all z: 'g^car. (('g^"*") (('g^"*") 'x 'y) 'z = ('g^"*") 'x (('g^"*") 'y 'z) in 'g^car)}; 'J['g] >- 'C['g] } -->
   sequent ['ext] { 'H; g: semigroup[i:l]; 'J['g] >- 'C['g] }   

interactive monoid_elim {| elim [] |} 'H 'J :
   sequent ['ext] { 'H; g: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car}; u: squash{.all x: 'g^car. all y: 'g^car. all z: 'g^car. (('g^"*") (('g^"*") 'x 'y) 'z = ('g^"*") 'x (('g^"*") 'y 'z) in 'g^car)}; v: squash{.all x: 'g^car. (('g^"*") ('g^"1") 'x = 'x in 'g^car & ('g^"*") 'x ('g^"1") = 'x in 'g^car)}; 'J['g] >- 'C['g] } -->
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
