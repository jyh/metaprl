(*
 * Group-like Objects.
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
 * Author: Xin Yu
 * Email : xiny@cs.caltech.edu
 *)

extends Itt_record
extends Itt_set
extends Itt_fun
extends Itt_disect

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

open Itt_fun

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare groupoid[i:l]
declare isCommutative{'g}
declare isSemigroup{'g}
declare semigroup[i:l]
declare csemigroup[i:l]
declare premonoid[i:l]
declare isMonoid{'g}
declare monoid[i:l]
declare cmonoid[i:l]

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval fold_groupoid : conv
topval fold_isSemigroup : conv
topval fold_semigroup1 : conv
topval fold_semigroup : conv
topval fold_premonoid1 : conv
topval fold_premonoid : conv
topval fold_isMonoid : conv
topval fold_monoid1 : conv
topval fold_monoid : conv
topval fold_isCommutative : conv
topval fold_csemigroup1 : conv
topval fold_csemigroup : conv
topval fold_cmonoid1 : conv
topval fold_cmonoid : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
