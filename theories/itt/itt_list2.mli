(*
 * Additional operations on lists.
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

extends Itt_list
extends Itt_logic
extends Itt_bool

open Refiner.Refiner.TermType

open Tactic_type.Conversionals

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Boolean test if a list is empty.
 *)
declare is_nil{'l}

(*
 * List membership.
 *)
declare mem{'x; 'l; 'T}

(*
 * The elements in one list are also in another.
 *)
declare \subset{'l1; 'l2; 'T}

(*
 * Two lists contain the same set of elements.
 *)
declare sameset{'l1; 'l2; 'T}

(*
 * Append two lists.
 *)
declare append{'l1; 'l2}

(*
 * Boolean universal quanitifer.
 *)
declare ball2{'l1; 'l2; x, y. 'b['x; 'y]}

(*
 * Association lists.
 *)
declare assoc{'eq; 'x; 'l; y. 'b['y]; 'z}
declare rev_assoc{'eq; 'x; 'l; y. 'b['y]; 'z}

(*
 * List map function.
 *)
declare map{'f; 'l}

(*
 * Fold a function over a list.
 *)
declare fold_left{'f; 'v; 'l}

(*
 * Length of the list.
 *)
declare length{'l}

(*
 * Get the nth element.
 *)
declare nth{'l; 'i}

(*
 * Replace the nth element.
 *)
declare replace_nth{'l; 'i; 't}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_append
prec prec_ball
prec prec_assoc

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

topval unfold_is_nil : conv
topval unfold_mem : conv
topval unfold_subset : conv
topval unfold_sameset : conv
topval unfold_append : conv
topval unfold_ball2 : conv
topval unfold_assoc : conv
topval unfold_rev_assoc : conv
topval unfold_map : conv
topval unfold_fold_left : conv
topval unfold_nth : conv
topval unfold_replace_nth : conv
topval unfold_length : conv

topval fold_is_nil : conv
topval fold_mem : conv
topval fold_subset : conv
topval fold_sameset : conv
topval fold_append : conv
topval fold_ball2 : conv
topval fold_assoc : conv
topval fold_rev_assoc : conv
topval fold_map : conv
topval fold_fold_left : conv
topval fold_nth : conv
topval fold_replace_nth : conv
topval fold_length : conv

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval samesetSymT : tactic
topval samesetTransT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
