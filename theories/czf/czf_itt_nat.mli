(*
 * Infinite set.
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

extends Czf_itt_singleton
extends Czf_itt_union
extends Czf_itt_empty

open Refiner.Refiner.Term

open Tactic_type.Tacticals
open Tactic_type.Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "inf"
declare zero
declare succ{'i}
declare lt{'i; 'j}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_zero : zero <--> empty

rewrite unfold_succ : succ{'i} <--> union{'i; sing{'i}}

rewrite unfold_inf : inf <-->
   collect{list{unit}; l. list_ind{'l; empty; h, t, g. succ{'g}}}

rewrite unfold_lt : lt{'i; 'j} <--> mem{'i; 'j}

topval fold_zero : conv
topval fold_succ : conv

topval natIndT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
