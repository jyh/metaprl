(*
 * Group.
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

extends Itt_record_label0
extends Czf_itt_dall

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

open Dtactic
open Auto_tactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare group{'g}
declare car{'g}         (* The "carrier" set for the group *)
declare op{'g; 'a; 'b}
declare id{'g}
declare inv{'g; 'a}

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Cancellation: a * b = a * c => b = c
 *)
topval groupCancelLeftT : int -> tactic

(*
 * Cancellation: b * a = c * a => b = c
 *)
topval groupCancelRightT : int -> tactic

(*
 * s1 * s = e => s1 = s'
 *)
topval uniqueInvLeftT : int -> tactic

(*
 * s * s1 = e => s1 = s'
 *)
topval uniqueInvRightT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
