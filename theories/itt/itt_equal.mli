(*
 * This module defines thepreliminary basis for the type
 * theory, including "type", universes, and equality rules.
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

include Tacticals

include Base_theory

include Itt_squash

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Tacticals
open Conversionals
open Base_theory

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "type"{'a}
declare univ[i:l]
declare equal{'T; 'a; 'b}
declare member{'T; 'x}
declare it
declare "true"
declare "false"
declare cumulativity[i:l, j:l]

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

rewrite unfold_member : member{'T; 'x} <--> ('x = 'x in 'T)

topval reduce_cumulativity : conv
topval fold_member : conv

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_type
prec prec_equal

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * True always holds.
 *)
rule trueIntro 'H :
   sequent ['ext] { 'H >- "true" }

(*
 * Typehood is equality.
 *)
rule equalityAxiom 'H 'J :
   sequent ['ext] { 'H; x: 'T; 'J['x] >- 'x = 'x in 'T }

(*
 * Reflexivity.
 *)
rule equalityRef 'H 'y :
   sequent ['ext] { 'H >- 'x = 'y in 'T } -->
   sequent ['ext] { 'H >- 'x = 'x in 'T }

(*
 * Symettry.
 *)
rule equalitySym 'H :
   sequent ['ext] { 'H >- 'y = 'x in 'T } -->
   sequent ['ext] { 'H >- 'x = 'y in 'T }

(*
 * Transitivity.
 *)
rule equalityTrans 'H 'z :
   sequent ['ext] { 'H >- 'x = 'z in 'T } -->
   sequent ['ext] { 'H >- 'z = 'y in 'T } -->
   sequent ['ext] { 'H >- 'x = 'y in 'T }

(*
 * H >- type ext a = b in T
 * by equalityFormation T
 *
 * H >- T ext a
 * H >- T ext b
 *)
rule equalityFormation 'H 'T :
   sequent ['ext] { 'H >- 'T } -->
   sequent ['ext] { 'H >- 'T } -->
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H >- (a1 = b1 in T1) = (a2 = b2 in T2) in Ui
 * by equalityEquality
 *
 * H >- T1 = T2 in Ui
 * H >- a1 = a2 in T1
 * H >- b1 = b2 in T1
 *)
rule equalityEquality 'H :
   sequent [squash] { 'H >- 'T1 = 'T2 in univ[i:l] } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'T1 } -->
   sequent [squash] { 'H >- 'b1 = 'b2 in 'T2 } -->
   sequent ['ext] { 'H >- ('a1 = 'b1 in 'T1) = ('a2 = 'b2 in 'T2) in univ[i:l] }

(*
 * Typehood.
 *)
rule equalityType 'H :
   sequent [squash] { 'H >- 'a = 'a in 'T } -->
   sequent [squash] { 'H >- 'b = 'b in 'T } -->
   sequent ['ext] { 'H >- "type"{. 'a = 'b in 'T } }

rule equalityTypeIsType 'H 'a 'b :
   sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- "type"{'T} }

(*
 * H >- it = it in (a = b in T)
 * by axiomEquality
 *
 * H >- a = b in T
 *)
rule axiomEquality 'H :
   sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- it = it in ('a = 'b in 'T) }

(*
 * H, x: a = b in T, J[x] >- C[x]
 * by equalityElimination i
 *
 * H, x: a = b in T; J[it] >- C[it]
 *)
rule equalityElimination 'H 'J :
   sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J['x] >- 'C['x] }

(*
 * H >- T = T in type
 * by typeEquality
 *
 * H >- T
 *)
rule typeEquality 'H :
   sequent [squash] { 'H >- 'T } -->
   sequent ['ext] { 'H >- "type"{'T} }

(*
 * Squash elim.
 *)
rule equality_squashElimination 'H :
   sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- 'a = 'b in 'T }

rule type_squashElimination 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent ['ext] { 'H >- "type"{'T} }

(*
 * H >- Uj = Uj in Ui
 * by universeEquality (side (j < i))
 *)
rule universeEquality 'H :
   sequent ['ext] { 'H >- cumulativity[j:l, i:l] } -->
   sequent ['ext] { 'H >- univ[j:l] = univ[j:l] in univ[i:l] }

(*
 * Universe is a type.
 *)
rule universeType 'H :
   sequent ['ext] { 'H >- "type"{univ[l:l]} }

(*
 * Anything in a universe is a type.
 *)
rule universeMemberType 'H univ[i:l] :
   sequent [squash] { 'H >- 'x = 'x in univ[i:l] } -->
   sequent ['ext] { 'H >- "type"{'x} }

(*
 * Derived form for known membership.
 *)
rule universeAssumType 'H 'J :
   sequent ['ext] { 'H; x: univ[l:l]; 'J['x] >- "type"{'x} }

(*
 * H >- Ui ext Uj
 * by universeFormation level{$j:l}
 *)
rule universeFormation 'H univ[j:l] :
   sequent ['ext] { 'H >- cumulativity[j:l, i:l] } -->
   sequent ['ext] {'H >- univ[i:l] }

(*
 * Squash from any.
 *)
rule squashFromAny 'H 'ext :
   sequent ['ext] { 'H >- 'T } -->
   sequent [squash] { 'H >- 'T }

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

type eqcd_data

resource (term * tactic, tactic, eqcd_data, meta_term * tactic) eqcd_resource

(*
 * Access to resources from toploop.
 *)
val get_resource : string -> eqcd_resource

topval eqcdT : tactic

(************************************************************************
 * PRIMITIVES AND TACTICS                                               *
 ************************************************************************)

val true_term : term
val is_true_term : term -> bool

val false_term : term
val is_false_term : term -> bool

val equal_term : term
val is_equal_term : term -> bool
val dest_equal : term -> term * term * term
val mk_equal_term : term -> term -> term -> term

val member_term : term
val is_member_term : term -> bool
val dest_member : term -> term * term
val mk_member_term : term -> term -> term

val type_term : term
val is_type_term : term -> bool
val mk_type_term : term -> term
val dest_type_term : term -> term

val univ_term : term
val univ1_term : term
val is_univ_term : term -> bool
val dest_univ : term -> level_exp
val mk_univ_term : level_exp -> term

val squash_term : term
val is_squash_term : term -> bool

val it_term : term

val d_equalT : int -> tactic
val eqcd_univT : tactic
val eqcd_itT : tactic
topval squash_equalT : tactic
topval squash_memberT : tactic
topval squash_typeT : tactic

(*
 * Typehood from truth.
 *)
topval typeAssertT : tactic

(*
 * Turn an eqcd tactic into a d tactic.
 *)
val d_wrap_eqcd : tactic -> int -> tactic
val wrap_intro : tactic -> int -> tactic
val wrap_elim : (int -> tactic) -> int -> tactic

topval memberAssumT : int -> tactic

topval unsquashT : term -> tactic
topval equalAssumT : int -> tactic
topval equalRefT : term -> tactic
topval equalSymT : tactic
topval equalTransT : term -> tactic
topval equalTypeT : term -> term -> tactic

topval univTypeT : term -> tactic
topval univAssumT : int -> tactic
topval cumulativityT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
