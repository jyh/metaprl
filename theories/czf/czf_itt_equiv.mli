(*
 * Equivalence relation.
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
 * Copyright (C) 2002 Xin Yu, Caltech
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
 * Email : xiny@cs.caltech.edu
 *)

extends Czf_itt_set
extends Czf_itt_member
extends Czf_itt_pair

open Itt_equal

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

open Itt_equal
open Itt_rfun
open Itt_struct

open Czf_itt_set

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare equiv{'s; 'r; 'a; 'b}
declare equiv{'s; 'r}
declare equiv_fun_set{'s; 'r; z. 'f['z]}
declare equiv_fun_prop{'s; 'r; z. 'P['z]}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

rewrite unfold_equiv : equiv{'s; 'r; 'a; 'b} <-->
   (((isset{'s} & isset{'r} & isset{'a} & isset{'b}) & mem{'a; 's} & mem{'b; 's}) & mem{pair{'a; 'b}; 'r})

rewrite unfold_equiv_fun_set : equiv_fun_set{'s; 'r; z. 'f['z]} <-->
   (all a: set. all b: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b} => equiv{'s; 'r; 'f['a]; 'f['b]}))

rewrite unfold_equiv_fun_prop : equiv_fun_prop{'s; 'r; z. 'P['z]} <-->
    (all a: set. all b: set. (equiv{'s; 'r} => equiv{'s; 'r; 'a; 'b} => 'P['a] => 'P['b]))

topval fold_equiv : conv

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_equiv_term : term -> bool
val mk_equiv_term : term -> term -> term -> term -> term
val dest_equiv : term -> term * term * term * term

val is_equiv_fun_set_term : term -> bool
val mk_equiv_fun_set_term : term -> term -> string -> term -> term
val dest_equiv_fun_set : term -> term * term * string * term

val is_equiv_fun_prop_term : term -> bool
val mk_equiv_fun_prop_term : term -> term -> string -> term -> term
val dest_equiv_fun_prop : term -> term * term * string * term

(*
 * Functionality.
 *)
topval equivFunSetT : int -> tactic
topval equivFunMemT : term -> int -> tactic

(*
 * Equivalence relations.
 *)
topval equivRefT : tactic
topval equivSymT : tactic
topval equivTransT : term -> tactic

topval equivSym1T : int -> tactic

(*
 * Substitution.
 *)
topval equivSubstT : term -> int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
