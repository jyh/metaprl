(*
 * List sorting demo.
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
 * Copyright (C) 1999 Jason Hickey, Cornell University
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

open Refiner.Refiner.TermType

open Tactic_type.Tactic

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Type for partial order.
 *)
declare partial_order{'A; 'lt}
declare compare_lt{'lt; 'a; 'b}

(*
 * Definition of being sorted.
 *)
declare sorted{'l; 'lt}
declare bounded{'u1; 'l; 'lt}

(*
 * Sorting algorithm.
 *)
declare insert{'u1; 'l; 'lt}
declare sort{'l; 'lt}

(************************************************************************
 * TACTICS AND CONVERSIONS                                              *
 ************************************************************************)

topval boundInclusionT : term -> tactic
topval insertInclusionT : tactic

topval fold_compare_lt : conv
topval fold_bounded : conv
topval fold_sorted : conv
topval fold_insert : conv
topval fold_sort : conv

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
