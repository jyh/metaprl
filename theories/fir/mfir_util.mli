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

open Tactic_type.Conversionals


(**************************************************************************
 * Declarations.
 **************************************************************************)

declare offset

declare do_tyApply{ 'poly_ty; 'ty_list }
declare instantiate_tyExists{ 'ty; 'var; 'num }
declare num_params{ 'ty }
declare nth_unionCase{ 'n; 'union_def }
declare union_cases{ 'set; 'cases }
declare index_of_subscript{ 'atom }


(**************************************************************************
 * Rewrites.
 **************************************************************************)

topval reduce_do_tyApply : conv
topval reduce_instantiate_tyExists : conv
topval reduce_num_params : conv
topval reduce_nth_unionCase : conv
topval reduce_union_cases : conv
topval reduce_index_of_subscript : conv
