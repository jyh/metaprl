(*
 * Defines term (de)construction operations for terms declared
 * in the FIR theory.
 *
 * ------------------------------------------------------------------------
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

open Opname
open Refiner.Refiner.Term

(* No parameters, no subterms. *)

val is_0_dep0_term : opname -> term -> bool

(* No parameters, 1 subterm. *)

val is_1_dep0_term : opname -> term -> bool
val mk_1_dep0_term : opname -> term -> term
val dest_1_dep0_term : opname -> term -> term

val is_0_dep0_1_dep1_term : opname -> term -> bool
val mk_0_dep0_1_dep1_term : opname -> string -> term -> term
val dest_0_dep0_1_dep1_term : opname -> term -> string * term

(* No parameters, 2 subterms. *)

val is_2_dep0_term : opname -> term -> bool
val mk_2_dep0_term : opname -> term -> term -> term
val dest_2_dep0_term : opname -> term -> term * term

val is_1_dep0_1_dep1_term : opname -> term -> bool
val mk_1_dep0_1_dep1_term : opname -> term -> string -> term -> term
val dest_1_dep0_1_dep1_term : opname -> term -> term * string * term

(* No parameters, 3 subterms. *)

val is_3_dep0_term : opname -> term -> bool
val mk_3_dep0_term : opname -> term -> term -> term -> term
val dest_3_dep0_term : opname -> term -> term * term * term

val is_2_dep0_1_dep1_term : opname -> term -> bool
val mk_2_dep0_1_dep1_term : opname -> term -> term -> string -> term -> term
val dest_2_dep0_1_dep1_term : opname -> term -> term * term * string * term

(* No parameters, 4 subterms. *)

val is_4_dep0_term : opname -> term -> bool
val mk_4_dep0_term : opname -> term -> term -> term -> term -> term
val dest_4_dep0_term : opname -> term -> term * term * term * term

val is_3_dep0_1_dep1_term : opname -> term -> bool
val mk_3_dep0_1_dep1_term : opname -> term -> term -> term -> string -> term -> term
val dest_3_dep0_1_dep1_term : opname -> term -> term * term * term * string * term

(* No parameters, 5 subterms. *)

val is_5_dep0_term : opname -> term -> bool
val mk_5_dep0_term : opname -> term -> term -> term -> term -> term -> term
val dest_5_dep0_term : opname -> term -> term * term * term * term * term

(* 1 parameter, 0 subterms. *)

val is_num_0_dep0_term : opname -> term -> bool
val mk_num_0_dep0_term : opname -> Mp_num.num -> term
val dest_num_0_dep0_term : opname -> term -> Mp_num.num

val is_str_0_dep0_term : opname -> term -> bool
val mk_str_0_dep0_term : opname -> string -> term
val dest_str_0_dep0_term : opname -> term -> string

(* 1 parameter, 1 subterms. *)

val is_num_1_dep0_term : opname -> term -> bool
val mk_num_1_dep0_term : opname -> Mp_num.num-> term -> term
val dest_num_1_dep0_term : opname -> term -> Mp_num.num * term

val is_str_1_dep0_term : opname -> term -> bool
val mk_str_1_dep0_term : opname -> string -> term -> term
val dest_str_1_dep0_term : opname -> term -> string * term

(* 1 parameter, 2 subterms. *)

val is_str_2_dep0_term : opname -> term -> bool
val mk_str_2_dep0_term : opname -> string -> term -> term -> term
val dest_str_2_dep0_term : opname -> term -> string * term * term

(* 1 parameter, 3 subterms. *)

val is_num_3_dep0_term : opname -> term -> bool
val mk_num_3_dep0_term : opname -> Mp_num.num -> term -> term -> term -> term
val dest_num_3_dep0_term : opname -> term -> Mp_num.num * term * term * term

(* 1 parameter, 4 subterms. *)

val is_str_3_dep0_1_dep1_term : opname -> term -> bool
val mk_str_3_dep0_1_dep1_term : opname -> string -> term -> term -> term -> string -> term -> term
val dest_str_3_dep0_1_dep1_term : opname -> term -> string * term * term * term * string * term

(* 2 parameters, 0 subterms. *)

val is_num_num_0_dep0_term : opname -> term -> bool
val mk_num_num_0_dep0_term : opname -> Mp_num.num -> Mp_num.num -> term
val dest_num_num_0_dep0_term : opname -> term -> Mp_num.num * Mp_num.num

val is_num_str_0_dep0_term : opname -> term -> bool
val mk_num_str_0_dep0_term : opname -> Mp_num.num -> string -> term
val dest_num_str_0_dep0_term : opname -> term -> Mp_num.num * string

val is_str_num_0_dep0_term : opname -> term -> bool
val mk_str_num_0_dep0_term : opname -> string -> Mp_num.num -> term
val dest_str_num_0_dep0_term : opname -> term -> string * Mp_num.num

(* 2 parameters, 1 subterm. *)

val is_num_str_1_dep0_term : opname -> term -> bool
val mk_num_str_1_dep0_term : opname -> Mp_num.num -> string -> term -> term
val dest_num_str_1_dep0_term : opname -> term -> Mp_num.num * string * term

(* 2 parameters, 2 subterms. *)

val is_num_str_2_dep0_term : opname -> term -> bool
val mk_num_str_2_dep0_term : opname -> Mp_num.num -> string -> term -> term -> term
val dest_num_str_2_dep0_term : opname -> term -> Mp_num.num * string * term * term

(* 3 parameters, 0 subterms. *)

val is_num_num_str_0_dep0_term : opname -> term -> bool
val mk_num_num_str_0_dep0_term : opname -> Mp_num.num -> Mp_num.num -> string -> term
val dest_num_num_str_0_dep0_term : opname -> term -> Mp_num.num * Mp_num.num * string

val is_num_str_num_0_dep0_term : opname -> term -> bool
val mk_num_str_num_0_dep0_term : opname -> Mp_num.num -> string -> Mp_num.num -> term
val dest_num_str_num_0_dep0_term : opname -> term -> Mp_num.num * string * Mp_num.num

(* 4 parameters, 0 subterms. *)

val is_num_str_num_num_0_dep0_term : opname -> term -> bool
val mk_num_str_num_num_0_dep0_term : opname -> Mp_num.num -> string -> Mp_num.num -> Mp_num.num -> term
val dest_num_str_num_num_0_dep0_term : opname -> term -> Mp_num.num * string * Mp_num.num * Mp_num.num

val is_num_str_num_str_0_dep0_term : opname -> term -> bool
val mk_num_str_num_str_0_dep0_term : opname -> Mp_num.num -> string -> Mp_num.num -> string -> term
val dest_num_str_num_str_0_dep0_term : opname -> term -> Mp_num.num * string * Mp_num.num * string
