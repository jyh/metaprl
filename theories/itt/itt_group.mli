(*
 * Groups.
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

extends Itt_grouplikeobj

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

declare pregroup[i:l]
declare isGroup{'g}
declare group[i:l]
declare abelg[i:l]
declare lcoset{'s; 'g; 'b}
declare rcoset{'s; 'g; 'b}
declare normalSubg[i:l]{'s; 'g}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_inv

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval fold_pregroup1 : conv
topval fold_pregroup : conv
topval fold_isGroup : conv
topval fold_group1 : conv
topval fold_group : conv
topval fold_abelg : conv
topval fold_lcoset : conv
topval fold_rcoset : conv
topval fold_normalSubg : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
