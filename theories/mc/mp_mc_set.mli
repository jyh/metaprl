(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Terms to represent sets used in the MC FIR.
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

include Base_theory
include Itt_bool
include Itt_list
include Itt_int_ext

open Refiner.Refiner.Term
open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Closed intervals.
 * 'left and 'right should be "sensible" left and right bounds.
 *)

declare interval{ 'left; 'right }

(*
 * int and rawint sets.
 * They're both comprised of a list (e.g. << cons{...} >>) of intervals.
 * The rawint_set also has to keep track of precision and signing.
 *)

declare int_set{ 'intervals }
declare rawint_set{ 'precision; 'sign; 'intervals }

(*
 * Membership tests.
 * These evaluate to btrue or bfalse (see rewrites below).
 * is_member reduces for both int_set and rawint_set.
 *)

declare in_interval{ 'num; 'interval }
declare is_member{ 'num; 'set }

(*************************************************************************
 * Rewrites.
 *************************************************************************)

topval reduce_in_interval : conv
topval reduce_is_member_int : conv
topval reduce_is_member_rawint: conv
topval reduce_is_member : conv

(*************************************************************************
 * Term operations.
 *************************************************************************)

val interval_term : term
val is_interval_term : term -> bool
val mk_interval_term : term -> term -> term
val dest_interval_term : term -> term * term

val int_set_term : term
val is_int_set_term : term -> bool
val mk_int_set_term : term -> term
val dest_int_set_term : term -> term

val rawint_set_term : term
val is_rawint_set_term : term -> bool
val mk_rawint_set_term : term -> term -> term -> term
val dest_rawint_set_term : term -> term * term * term
