(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Operations for converting between MC Fir types and MetaPRL terms.
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
open Fir

(* Open MetaPRL ML namespaces. *)

open Refiner.Refiner.Term

(*
 * Convert to and from int_precision, int_signed, and float_precision.
 *)

val term_of_int_precision : int_precision -> term
val int_precision_of_term : term -> int_precision

val term_of_int_signed : int_signed -> term
val int_signed_of_term : term -> int_signed

val term_of_float_precision : float_precision -> term
val float_precision_of_term : term -> float_precision

(*
 * Convert to and from ty_var.
 *)

val term_of_ty_var : ty_var -> term
val ty_var_of_term : term -> ty_var

(*
 * Convert to and from ty.
 *)

val term_of_ty : ty -> term
val ty_of_term : term -> ty

(*
 * Convert to and from union_type.
 *)

val term_of_union_type : union_type -> term
val union_type_of_term : term -> union_type
