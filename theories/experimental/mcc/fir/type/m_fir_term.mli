(*
 * Instruction destruction and creation.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
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
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends M_fir

open Refiner.Refiner.TermType

open Fir

(*
 * Term forms.
 *)
type term_ty   = term poly_ty
type term_atom = (term, term) poly_atom
type term_exp  = (term, term, term) poly_exp

(* No delayed substitutions *)
type exp       = (ty, atom, exp) poly_exp

(*
 * Main destructors.
 *)
val dest_type : term -> ty
val dest_atom : term -> atom
val dest_exp  : term -> exp

val dest_type_term : term -> term_ty
val dest_atom_term : term -> term_atom
val dest_exp_term  : term -> term_exp

(*
 * Make constructors.
 *)
val make_type      : ty -> term
val make_atom      : atom -> term
val make_exp       : exp -> term

val make_type_term : term_ty -> term
val make_atom_term : term_atom -> term
val make_exp_term  : term_exp -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
