(*
 * The Mfir_int_set module implements sets of integers.
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

extends Mfir_bool
extends Mfir_int
extends Mfir_list

open Tactic_type.Conversionals


(**************************************************************************
 * Declarations.
 **************************************************************************)

(*
 * Integer sets.
 *)

declare interval{ 'left; 'right }
declare intset{ 'interval_list }
declare rawintset[precision:n, sign:s]{ 'interval_list }

(*
 * Set operations.
 *)

declare member{ 'num; 's }
declare subset{ 'smaller_set; 'larger_set }
declare set_eq{ 'set1; 'set2 }

declare singleton{ 'i }

(*
 * Constants.
 *)

declare intset_max
declare enum_max
declare rawintset_max[precision:n, sign:s]


(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*
 * Set operations.
 *)

topval reduce_member_interval : conv
topval reduce_member_intset_ind : conv
topval reduce_member_intset_base : conv
topval reduce_member_rawintset_ind : conv
topval reduce_member_rawintset_base : conv

topval reduce_subset_base : conv
topval reduce_subset_ind : conv
topval reduce_set_eq : conv
topval reduce_singleton : conv

(*
 * Constants.
 *)

topval reduce_intset_max : conv
topval reduce_enum_max : conv
topval reduce_rawintset_max_u8 : conv
topval reduce_rawintset_max_s8 : conv
topval reduce_rawintset_max_u16 : conv
topval reduce_rawintset_max_s16 : conv
topval reduce_rawintset_max_u32 : conv
topval reduce_rawintset_max_s32 : conv
topval reduce_rawintset_max_u64 : conv
topval reduce_rawintset_max_s64 : conv
