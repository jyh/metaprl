(*
 * These are the basic terms and axioms of TPTP.
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
 *)

extends Itt_theory

open Lm_symbol

open Refiner.Refiner.TermType

open Tactic_type.Conversionals
open Tactic_type.Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "t"

define unfold_atom0 : atom0 <-->
                          atom
define unfold_atom1 : atom1 <-->
                          (atom0 -> atom0)
define unfold_atom2 : atom2 <-->
                          (atom0 -> atom0 -> atom0)
define unfold_atom3 : atom3 <-->
                          (atom0 -> atom0 -> atom0 -> atom0)
define unfold_atom4 : atom4 <-->
                          (atom0 -> atom0 -> atom0 -> atom0 -> atom0)
define unfold_atom5 : atom5 <-->
                          (atom0 -> atom0 -> atom0 -> atom0 -> atom0 -> atom0)

define unfold_prop0 : prop0 <-->
                          univ[1:l]
define unfold_prop1 : prop1 <-->
                          (atom0 -> univ[1:l])
define unfold_prop2 : prop2 <-->
                          (atom0 -> atom0 -> univ[1:l])
define unfold_prop3 : prop3 <-->
                          (atom0 -> atom0 -> atom0 -> univ[1:l])
define unfold_prop4 : prop4 <-->
                          (atom0 -> atom0 -> atom0 -> atom0 -> univ[1:l])
define unfold_prop5 : prop5 <-->
                          (atom0 -> atom0 -> atom0 -> atom0 -> atom0 -> univ[1:l])

define unfold_apply2 : "apply"{'f1; 'x1; 'x2} <--> ('f1 'x1 'x2)
define unfold_apply3 : "apply"{'f1; 'x1; 'x2; 'x3} <--> ('f1 'x1 'x2 'x3)
define unfold_apply4 : "apply"{'f1; 'x1; 'x2; 'x3; 'x4} <--> ('f1 'x1 'x2 'x3 'x4)
define unfold_apply5 : "apply"{'f1; 'x1; 'x2; 'x3; 'x4; 'x5} <--> ('f1 'x1 'x2 'x3 'x4 'x5)

(* All and exists are always bound over atom0 *)
define unfold_atomic : "atomic"{'x} <--> ('x in atom0)
define unfold_all : "all"{v. 'b['v]} <--> Itt_logic!"all"{atom0; v. 'b['v]}
define unfold_exists : "exists"{v. 'b['v]} <--> Itt_logic!"exists"{atom0; v. 'b['v]}

topval fold_atom0 : conv
topval fold_atom1 : conv
topval fold_atom2 : conv
topval fold_atom3 : conv
topval fold_atom4 : conv
topval fold_atom5 : conv

topval fold_prop0 : conv
topval fold_prop1 : conv
topval fold_prop2 : conv
topval fold_prop3 : conv
topval fold_prop4 : conv
topval fold_prop5 : conv

topval fold_apply2 : conv
topval fold_apply3 : conv
topval fold_apply4 : conv
topval fold_apply5 : conv

topval fold_atomic : conv
topval fold_all : conv
topval fold_exists : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(************************************************************************
 * OPERATIONS                                                           *
 ************************************************************************)

(*
 * Nested terms.
 *)
val t_term : term
val is_t_term : term -> bool

val is_atomic_term : term -> bool
val mk_atomic_term : term -> term
val dest_atomic : term -> term

val is_apply_term : term -> bool
val mk_apply_term : term list -> term
val dest_apply : term -> term list
val arity_of_apply : term -> int
val head_of_apply : term -> term

val mk_or_term : term list -> term
val dest_or : term -> term list

val mk_and_term : term list -> term
val dest_and : term -> term list

val is_all_term : term -> bool
val mk_all_term : var list -> term -> term
val dest_all : term -> var list * term
val var_of_all : term -> var

val is_exists_term : term -> bool
val mk_exists_term : var list -> term -> term
val dest_exists : term -> var list * term
val var_of_exists : term -> var

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * This is for proving intro rules.
 *)
topval tptp_autoT : tactic

topval t_atomic : tactic
topval atomicT : int -> tactic
topval typeT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
