(*
 * Normal subgroup.
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
include Czf_itt_subgroup
include Czf_itt_coset

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

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

(*
 * A subgroup H of a group G is normal if its left and right cosets
 * coincide, that is, if gH = Ha for all g in G.
 *)
declare normal_subg{'s; 'g}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

rewrite unfold_normal_subg : normal_subg{'s; 'g} <-->
   (subgroup{'s; 'g} & (all a: set. (mem{'a; car{'g}} => equal{lcoset{'s; 'g; 'a}; rcoset{'s; 'g; 'a}})))

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(* This is the same as setExtT in Czf_itt_member.
(*
 * There is a standared way to show that two sets are equal;
 * show that each is a subset of the other.
 *)
topval equalSubsetT : tactic
*)

(*
 * All subgroups of abelian groups are normal.
 *)
topval abelNormalSubgT : term -> int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
