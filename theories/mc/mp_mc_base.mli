(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Provides basic code for debugging and term
 * construction / deconstruction.
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

open Opname
open Refiner.Refiner.Term

(*************************************************************************
 * Debugging.
 ************************************************************************)

(* Set this to true to enable debugging output from the functions below. *)

val debug : bool ref

(*
 * If debug is set to true, then the following will output
 * the given string or term.  Otherwise, they do nothing.
 *)

val debug_string : string -> unit
val debug_term : term -> unit

(*************************************************************************
 * Term operations.
 *************************************************************************)

(*
 * The functions here are essentially the same in function as those
 * in Refiner.Refiner.TermOp, though the naming scheme is different.
 *
 * The function naming scheme here is as follows:
 * X_depY pairs represent X terms in a row, each with Y bound variables.
 * The strings for a given subterm with bound variables come right
 * before the term they appear in both function parameters and
 * return values.
 *
 * The dest_* functions will throw RefineError's if they are given
 * incorrectly structured terms (or if there is an internal
 * error in my code).
 *)

(*
 * 4 subterms.
 *)

val is_4_dep0_term : opname -> term -> bool
val mk_4_dep0_term : opname -> term -> term -> term -> term -> term
val dest_4_dep0_term : opname -> term -> term * term * term * term

val is_3_dep0_1_dep1_term : opname -> term -> bool
val mk_3_dep0_1_dep1_term :
   opname -> term -> term -> term -> string -> term -> term
val dest_3_dep0_1_dep1_term :
   opname -> term -> term * term * term * string * term

(*
 * 5 subterms.
 *)

val is_5_dep0_term : opname -> term -> bool 
val mk_5_dep0_term : opname -> term -> term -> term -> term -> term -> term
val dest_5_dep0_term : opname -> term -> term * term * term * term * term

val is_4_dep0_1_dep1_term : opname -> term -> bool
val mk_4_dep0_1_dep1_term :
   opname -> term -> term -> term -> term -> string -> term -> term
val dest_4_dep0_1_dep1_term :
   opname -> term -> term * term * term * term * string * term

(*
 * 6 subterms.
 *)

val is_6_dep0_term : opname -> term -> bool
val mk_6_dep0_term :
   opname -> term -> term -> term -> term -> term -> term -> term
val dest_6_dep0_term :
   opname -> term -> term * term * term * term * term * term

val is_5_dep0_1_dep1_term : opname -> term -> bool
val mk_5_dep0_1_dep1_term :
   opname -> term -> term -> term -> term -> term -> string -> term -> term
val dest_5_dep0_1_dep1_term :
   opname -> term -> term * term * term * term * term * string * term

(*
 * 7 subterms
 *)

val is_7_dep0_term : opname -> term -> bool
val mk_7_dep0_term :
   opname -> term -> term -> term -> term -> term -> term -> term -> term
val dest_7_dep0_term :
   opname -> term -> term * term * term * term * term * term * term

(*
 * 8 subterms
 *)

val is_8_dep0_term : opname -> term -> bool
val mk_8_dep0_term :
   opname -> term -> term -> term -> term ->
             term -> term -> term -> term -> term
val dest_8_dep0_term :
   opname -> term -> term * term * term * term * term * term * term * term
