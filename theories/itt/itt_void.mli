(*
 * Here are rules for the Void base type.
 * Void has no elements.  Its propositional
 * interpretation is "False".
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
 *
 *)

extends Itt_equal
extends Itt_subtype

open Refiner.Refiner.Term
open Tactic_type.Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare void

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Void
 * by voidFormation
 *)
rule voidFormation : sequent { <H> >- univ[i:l] }

(*
 * H >- Void = Void in Ui ext Ax
 * by voidEquality
 *)
rule voidEquality : sequent { <H> >- void in univ[i:l] }

(*
 * Typehood.
 *)
rule voidType : sequent { <H> >- "type"{void} }

(*
 * H; i:x:Void; J >- C
 * by voidElimination i
 *)
rule voidElimination 'H : sequent { <H>; x: void; <J['x]> >- 'C['x] }

(*
 * Subtyping.
 *)
rule void_subtype :
   sequent { <H> >- \subtype{void; 'T} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val void_term : term
val top_term : term (* used in type inference *)
val is_void_term : term -> bool

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
