(*
 * Subgroup.
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

include Czf_itt_group
include Czf_itt_subset
include Czf_itt_isect

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Sequent
open Tactic_type.Tacticals
open Var
open Mptop

open Base_dtactic
open Base_auto_tactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare subgroup{'s; 'g}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

rewrite unfold_subgroup : subgroup{'s; 'g} <-->
   (group{'s} & group{'g} & subset{car{'s}; car{'g}} & (all a: set. all b: set. (mem{'a; car{'s}} => mem{'b; car{'s}} => eq{op{'s; 'a; 'b}; op{'g; 'a; 'b}})))

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * The intersection of subgroups H1 and H2 of a group G
 * is again a subgroup of G.
 *)
topval subgroupIsectT: term -> term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
