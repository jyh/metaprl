(*
 * Atom is the type of tokens (strings)
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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

(*
 * Derived from baseTheory.
 *)
include Itt_equal

open Refiner.Refiner.Term

open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare atom
declare token[@t:t]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Atom
 * by atomFormation
 *)
axiom atomFormation 'H : sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- Atom = Atom in Ui ext Ax
 * by atomEquality
 *)
axiom atomEquality 'H : sequent ['ext] { 'H >- atom = atom in univ[@i:l] }

(*
 * Typehood.
 *)
axiom atomType 'H : sequent ['ext] { 'H >- "type"{atom} }

(*
 * H >- Atom ext "t"
 * by tokenFormation "t"
 *)
axiom tokenFormation 'H token[@t:t] : sequent ['ext] { 'H >- atom }

(*
 * H >- "t" = "t" in Atom
 * by tokenEquality
 *)
axiom tokenEquality 'H : sequent ['ext] { 'H >- token[@t:t] = token[@t:t] in atom }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_atomT : int -> tactic
val eqcd_atomT : tactic
val eqcd_tokenT : tactic

val atom_term : term

val token_term : term
val bogus_token : term
val is_token_term : term -> bool
val dest_token : term -> string
val mk_token_term : string -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "manager"
 * End:
 * -*-
 *)
