(*
 * Basic operations for converting MCC FIR types to/from MetaPRL terms.
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

open Fir

(* Open MetaPRL ML namespaces. *)

open Refiner.Refiner.Term


(*
 * Convert to and from ty.
 *)

val term_of_ty : ty -> term
val ty_of_term : term -> ty


(*
 * Convert to and from mutable_flag and mutable_ty.
 *)

val term_of_mutable_flag : mutable_flag -> term
val mutable_flag_of_term : term -> mutable_flag

val term_of_mutable_ty : mutable_ty -> term
val mutable_ty_of_term : term -> mutable_ty


(*
 * Convert to and from tydef.
 *)

val term_of_tydef : tydef -> term
val tydef_of_term : term -> tydef


(*
 * Convert to and from frame.
 *)

val term_of_frame : frame -> term
val frame_of_term : term -> frame
