(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Basic operations for converting between the MC Fir and
 * and MetaPRL terms.
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
 * Author: Brian Emre Aydemir
 * Email:  emre@its.caltech.edu
 *)

(* Open MC ML namespaces. *)

open Rawint
open Rawfloat
open Symbol

(* Open MetaPRL ML namespaces. *)

open Refiner.Refiner.Term

(*
 * Convert between symbols and variable terms.
 * A variable term is << 'a >> (for example).
 *)

val var_term_of_symbol : symbol -> term
val symbol_of_var_term : term -> symbol (* THIS NEEDS FIXING! *)

(*
 * Convert between integer and floating point constants and numbers.
 * A number term is number[i:n] (for example).
 * Rawfloats are represented as integers!
 *)

val number_term_of_int : int -> term
val int_of_number_term : term -> int

val number_term_of_rawint : rawint -> term
val rawint_of_number_term : int_precision -> int_signed -> term -> rawint

(* THESE NEED CHECKING (MORE SO THAN OTHER FUNCS) *)
val number_term_of_rawfloat : rawfloat -> term
val rawfloat_of_number_term : float_precision -> term -> rawfloat

(*
 * Convert a list to a "term list", i.e. << cons{ ... } >>.
 * For term_of_list:
 *    ('a -> term)   -- converts an item of type 'a to a corresponding term.
 * For list_of_term:
 *    (term -> 'a)   -- converts a term representing an 'a to an 'a.
 *)

val term_of_list : ('a -> term) -> 'a list -> term
val list_of_term : (term -> 'a) -> term -> 'a list
