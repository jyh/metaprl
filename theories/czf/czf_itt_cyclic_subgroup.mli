(*
 * Cyclic subgroup.
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

extends Czf_itt_group_power
extends Czf_itt_subgroup

open Refiner.Refiner.RefineError

open Tactic_type.Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare cyc_subg{'s; 'g; 'a}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

rewrite unfold_cyc_subg : cyc_subg{'s; 'g; 'a} <-->
   (group{'s} & group{'g} & mem{'a; car{'g}} & equal{car{'s}; sep{car{'g}; x. (exst n: int. eq{'x; power{'g; 'a; 'n}})}} & (all a: set. all b: set. (mem{'a; car{'s}} => mem{'b; car{'s}} => eq{op{'s; 'a; 'b}; op{'g; 'a; 'b}})))

topval fold_cyc_subg : conv

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * cyc_subg{'s; 'g; 'a} => subgroup{'s; 'g}
 *)
topval cycsubgSubgroupT: term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
