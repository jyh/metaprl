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

extends Czf_itt_subgroup
extends Czf_itt_coset

open Refiner.Refiner.RefineError

open Tactic_type.Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * A subgroup H of a group G is normal if its left and right cosets
 * coincide, that is, if aH = Ha for all a in G.
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
