(*
 * Basic operations for converting between the MCC FIR and
 * and MetaPRL terms.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

(* Open MCC ML namespaces. *)

open Rawint
open Rawfloat
open Symbol
open Fir

(* Open MetaPRL ML namespaces. *)

open Refiner.Refiner.Term


(*
 * Print out the given term, and then raise a RefineError.
 * The string parameter should be the name of the function
 * raising the error.
 *)

val report_error : string -> term -> 'a


(*
 * Convert between symbols and terms.
 *)

val term_of_symbol : symbol -> term
val symbol_of_term : term -> symbol


(*
 * Convert to and from options.
 *)

val term_of_option : ('a -> term) -> 'a option -> term
val option_of_term : (term -> 'a) -> term -> 'a option


(*
 * Convert to and from bool values.
 *)

val term_of_bool : bool -> term
val bool_of_term : term -> bool


(*
 * Convert between (raw) integers and number terms.
 *)

val number_term_of_int : int -> term
val int_of_number_term : term -> int

val number_term_of_rawint : rawint -> term
val rawint_of_number_term : int_precision -> int_signed -> term -> rawint


(*
 * Convert int_precision, int_signed, and float_precision.
 *)

val num_of_int_precision : int_precision -> Mp_num.num
val int_precision_of_num : Mp_num.num -> int_precision

val string_of_int_signed : int_signed -> string
val int_signed_of_string : string -> int_signed

val num_of_float_precision : float_precision -> Mp_num.num
val float_precision_of_num : Mp_num.num -> float_precision


(*
 * Convert a list to a "term list", i.e. << cons{ ... } >>.
 * Lists are assumed to be nil-terminated.
 * For term_of_list:
 *    ('a -> term)   -- converts an item of type 'a to a corresponding term.
 * For list_of_term:
 *    (term -> 'a)   -- converts a term representing an 'a to an 'a.
 *)

val term_of_list : ('a -> term) -> 'a list -> term
val list_of_term : (term -> 'a) -> term -> 'a list


(*
 * Convert (raw) integer sets to terms.
 *)

val term_of_int_set : int_set -> term
val int_set_of_term : term -> int_set

val term_of_rawint_set : rawint_set -> term
val rawint_set_of_term : term -> rawint_set

val term_of_set : set -> term
val set_of_term : term -> set
