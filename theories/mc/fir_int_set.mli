(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define a limited version of the int_set type from the FIR.
 * It's limited in the sense that I don't implement all the
 *    possible operations that the FIR int_set has.
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
include Itt_int_ext

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Bounds.
 * Here for completeness.
 *)
declare open_bound{ 'num }
declare inf_bound

(*
 * Intervals.
 * Represents a closed interval in the integers.
 * 'left and 'right should be numbers with 'left <= 'right.
 *)
declare interval{ 'left; 'right }

(*
 * The set.
 * 'intervals should be a list of intervals, or nil in order to
 *    represent the empty set.
 *)
declare int_set{ 'intervals }

(*
 * Short form.
 * For convinience.  Declares a set consisting of the closed
 *    interval [a,b].
 *)
declare int_set{ 'a; 'b }

(*
 * Member test.
 * in_interval reduces to btrue if 'num is in the interval and
 *    bfalse otherwise.
 * member reduces to btrue if 'num is in 'int_set and bfalse otherwise.
 *    'num is in 'int_set if it's in any one of the intervals of the set.
 * not_in_interval and not_member are the negations of the above.
 *)
define unfold_in_interval :
   in_interval{ 'num; interval{'l; 'r} } <-->
   band{ le_bool{'l; 'num}; le_bool{'num; 'r} }
declare member{ 'num; 'int_set }

(*************************************************************************
 * Rewrites.
 *************************************************************************)

topval unfold_in_interval : conv
topval reduce_member_cons : conv
topval reduce_member_nil : conv
topval reduce_short_int_set : conv
