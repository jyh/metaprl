(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Basic operations for converting between the MC Fir and
 * MetaPRL terms.
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
open Symbol

(* Open MetaPRL ML namespaces. *)

open Mp_num
open Refiner.Refiner.Term
open Itt_int_base

(*
 * Convert between symbols and variable terms (e.g. 'a).
 *)

let var_term_of_symbol s =
   mk_var_term (string_of_symbol s)

(*
let symbol_of_var_term v =
   (dest_var v) (* so I have a string now... now what? ... *)
*)

(*
 * Convert between integer constants and numbers.
 *)

let number_term_of_int i =
   mk_number_term (num_of_int i)

let int_of_number_term n =
   int_of_num (dest_number n)

let number_term_of_rawint r =
   mk_number_term (num_of_string (Rawint.to_string r))

let rawint_of_number_term precision sign t =
   Rawint.of_string precision sign (string_of_num (dest_number t))
