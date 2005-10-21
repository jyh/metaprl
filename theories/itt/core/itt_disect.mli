(*
 * Dependent intersection type.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
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
 *
 *)

extends Itt_equal
extends Itt_set
extends Itt_isect
extends Itt_subtype

open Basic_tactics

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare bisect{'A; x. 'B['x]}

val is_disect_term : term -> bool
val dest_disect : term -> var * term * term
val mk_disect_term : var -> term -> term -> term

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

rule dintersectionTypeElimination 'H 'a :
   [wf] sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; <J['u]>  >- 'a in 'A } -->
   sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; v:"type"{'B['a]}; <J['u]> >- 'C['u] } -->
   sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; <J['u]> >- 'C['u] }



(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval disectCaseEqualityT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
