(*!
 * @spelling{isCommutative csemigroup cmonoid abelg}
 *
 * @begin[doc]
 * @module[Itt_abelian_group]
 *
 * This theory defines commutative semigroup, commutative monoid,
 * and abelian group.
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
extends Itt_group
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
open Itt_logic
open Itt_int_ext

let _ =
   show_loading "Loading Itt_abelian_group%t"

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * @end[doc]
 *)
define unfold_isCommutative : isCommutative{'g} <-->
   all x: 'g^car. all y: 'g^car. (('g^"*") 'x 'y = ('g^"*") 'y 'x in 'g^car)

define unfold_csemigroup1 : csemigroup[i:l] <-->
   {g: groupoid[i:l] | isSemigroup{'g} & isCommutative{'g}}

define unfold_cmonoid1 : cmonoid[i:l] <-->
   {g: premonoid[i:l] | (isMonoid{'g}) & isCommutative{'g}}

define unfold_abelg1 : abelg[i:l] <-->
   {g: pregroup[i:l] | isGroup{'g} & isCommutative{'g}}
(*! @docoff *)

interactive_rw unfold_csemigroup :
   csemigroup[i:l] <--> {car: univ[i:l]; "*": ^car -> ^car -> ^car; (all x: ^car. all y: ^car. all z: ^car. ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^car) & (all x: ^car. all y: ^car. 'x ^* 'y = 'y ^* 'x in ^car)}

interactive_rw unfold_cmonoid :
   cmonoid[i:l] <--> {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; ((all x: ^car. all y: ^car. all z: ^car. ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^car) & (all x: ^car. (^"1" ^* 'x = 'x in ^car & 'x ^* ^"1" = 'x in ^car))) & (all x: ^car. all y: ^car. 'x ^* 'y = 'y ^* 'x in ^car)}

interactive_rw unfold_abelg :
   abelg[i:l] <--> {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car; inv: ^car -> ^car; ((all x: ^car. all y: ^car. all z: ^car. ('x ^* 'y) ^* 'z = 'x ^* ('y ^* 'z) in ^car) & (all x: ^car. ^"1" ^* 'x = 'x in ^car) & (all x: ^car. ((^inv) 'x) ^* 'x = ^"1" in ^car)) & (all x: ^car. all y: ^car. 'x ^* 'y = 'y ^* 'x in ^car)}

let fold_isCommutative = makeFoldC << isCommutative{'g} >> unfold_isCommutative
let fold_csemigroup1 = makeFoldC << csemigroup[i:l] >> unfold_csemigroup1
let fold_csemigroup = makeFoldC << csemigroup[i:l] >> unfold_csemigroup
let fold_cmonoid1 = makeFoldC << cmonoid[i:l] >> unfold_cmonoid1
let fold_cmonoid = makeFoldC << cmonoid[i:l] >> unfold_cmonoid
let fold_abelg1 = makeFoldC << abelg[i:l] >> unfold_abelg1
let fold_abelg = makeFoldC << abelg[i:l] >> unfold_abelg

let csemigroupDT n = rw unfold_csemigroup n thenT dT n
let cmonoidDT n = rw unfold_cmonoid n thenT dT n
let abelgDT n = rw unfold_abelg n thenT dT n

let resource elim +=
   [<<csemigroup[i:l]>>, csemigroupDT;
    <<cmonoid[i:l]>>, cmonoidDT;
    <<abelg[i:l]>>, abelgDT
   ]

let resource intro +=
   [<<csemigroup[i:l]>>, wrap_intro (csemigroupDT 0);
    <<cmonoid[i:l]>>, wrap_intro (cmonoidDT 0);
    <<abelg[i:l]>>, wrap_intro (abelgDT 0)
   ]

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform isCommutative_df : except_mode[src] :: isCommutative{'g} =
   `"isCommutative(" slot{'g} `")"

dform csemigroup_df1 : except_mode[src] :: csemigroup[i:l] =
   math_csemigroup{slot[i:l]}

dform cmonoid_df1 : except_mode[src] :: cmonoid[i:l] =
   math_cmonoid{slot[i:l]}

dform abelg_df : except_mode[src] :: abelg[i:l] =
   math_abelg{slot[i:l]}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive csemigroup_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{csemigroup[i:l]} }

interactive cmonoid_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{cmonoid[i:l]} }

interactive abelg_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{abelg[i:l]} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
