(*
 * The Mfir_util module defines terms and rewrites for working
 * with the MetaPRL representation of the FIR.
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

extends Mfir_int
extends Mfir_list
extends Mfir_int_set
extends Mfir_ty
extends Mfir_exp
extends Mfir_sequent

open Tactic_type.Conversionals


(**************************************************************************
 * Declarations.
 **************************************************************************)

(*
 * Offset type.
 *)

declare offset


(*
 * Definition extraction.
 *)

declare get_core{ 'poly_ty }


(*
 * Type application.
 *)

declare apply_types{ 'poly_ty; 'ty_list }


(*
 * Parameter counting.
 *)

declare num_params{ 'ty }


(*
 * Existential unpacking.
 *)

declare unpack_exists{ 'ty; 'var; 'num }


(*
 * Union of match cases.
 *)

declare union_cases{ 'set; 'cases }


(*
 * Conversions.
 *)

declare index_of_subscript{ 'atom }
declare ty_of_mutable_ty{ 'mutable_ty }


(**************************************************************************
 * Rewrites.
 **************************************************************************)

topval reduce_get_core : conv
topval reduce_apply_types : conv
topval reduce_num_params : conv
topval reduce_unpack_exists : conv
topval reduce_union_cases : conv
topval reduce_index_of_subscript : conv
topval reduce_ty_of_mutable_ty : conv
