(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Basic operations for converting between the MC FIR and
 * and MetaPRL terms.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
open Fir

(* Open MetaPRL ML namespaces. *)

open Refiner.Refiner.Term

(*************************************************************************
 * Basic conversions.
 *************************************************************************)

(*
 * Convert between var's, ty_var's, label's, and terms.
 *)

val term_of_var : var -> term
val var_of_term : term -> var
val string_of_var : var -> string
val var_of_string : string -> var

val term_of_ty_var : ty_var -> term
val ty_var_of_term : term -> ty_var
val string_of_ty_var : ty_var -> string
val ty_var_of_string : string -> ty_var

val term_of_label : label -> term
val label_of_term : term -> label
val string_of_label : label -> string
val label_of_string : string -> label

(*
 * Convert between integer and floating point constants and numbers.
 * A number term is number[i:n].
 *)

val number_term_of_int : int -> term
val int_of_number_term : term -> int

val number_term_of_rawint : rawint -> term
val rawint_of_number_term : int_precision -> int_signed -> term -> rawint

val number_term_of_rawfloat : rawfloat -> term
val rawfloat_of_number_term : float_precision -> term -> rawfloat

(*
 * Convert to and from string values.
 *)

val term_of_string : string -> term
val string_of_term : term -> string

(*
 * Convert a list to a "term list", i.e. << cons{ ... } >>.
 * For term_of_list:
 *    ('a -> term)   -- converts an item of type 'a to a corresponding term.
 * For list_of_term:
 *    (term -> 'a)   -- converts a term representing an 'a to an 'a.
 *)

val term_of_list : ('a -> term) -> 'a list -> term
val list_of_term : (term -> 'a) -> term -> 'a list

(*************************************************************************
 * Conversions for terms in Mp_mc_fir_base.
 *************************************************************************)

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
 * Convert to and from int_precision and float_precision.
 *)

val term_of_int_precision : int_precision -> term
val int_precision_of_term : term -> int_precision

val term_of_float_precision : float_precision -> term
val float_precision_of_term : term -> float_precision

(*
 * Convert to and from int_signed.
 *)

val term_of_int_signed : int_signed -> term
val int_signed_of_term : term -> int_signed

(*
 * Convert to and from int_set, rawint_set, and set.
 *)

val term_of_int_set : int_set -> term
val int_set_of_term : term -> int_set

val term_of_rawint_set : rawint_set -> term
val rawint_set_of_term : term -> rawint_set

val term_of_set : set -> term
val set_of_term : term -> set

(*
 * Convert to and from tuple_class.
 *)

val term_of_tuple_class : tuple_class -> term
val tuple_class_of_term : term -> tuple_class

(*
 * Convert to and from union_type.
 *)

val term_of_union_type : union_type -> term
val union_type_of_term : term -> union_type
