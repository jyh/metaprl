(*
 * Cosets.
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
include Czf_itt_set_bvd

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
 * Let H be a subgroup of a group G. The subset aH = {ah | h in H}
 * is the left coset of H containing a, while Ha = {ha | h in H}
 * is the right coset of H containing a.
 *)
declare lcoset{'h; 'g; 'a}
declare rcoset{'h; 'g; 'a}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

rewrite unfold_lcoset : lcoset{'h; 'g; 'a} <-->
   sep{car{'g}; x. "dexists"{car{'h}; y. mem{pair{'x; op{'g; 'a; 'y}}; eqG{'g}}}}

rewrite unfold_rcoset : rcoset{'h; 'g; 'a} <-->
   sep{car{'g}; x. "dexists"{car{'h}; y. mem{pair{'x; op{'g; 'y; 'a}}; eqG{'g}}}}

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
