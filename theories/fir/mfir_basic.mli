(*
 * The Mfir_basic module declares basic terms needed to
 * support the MetaPRL representation of the FIR.
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

extends Base_theory

open Tactic_type.Conversionals

(**************************************************************************
 * Declarations.
 **************************************************************************)

(*
 * Booleans.
 *)

declare "true"
declare "false"
declare "or"{ 'bool1; 'bool2 }
declare "and"{ 'bool1; 'bool2 }
declare "not"{ 'boolean }
declare ifthenelse{ 'test; 'true_case; 'false_case }

(*
 * Integers.
 *)

declare number[i:n]
declare numeral{ 'num }
declare add{ 'num1; 'num2 }
declare sub{ 'num1; 'num2 }
declare mul{ 'num1; 'num2 }
declare div{ 'num1; 'num2 }
declare rem{ 'num1; 'num2 }
declare minus{ 'num }

declare int_eq{ 'num1; 'num2 }
declare int_neq{ 'num1; 'num2 }
declare int_lt{ 'num1; 'num2 }
declare int_le{ 'num1; 'num2 }
declare int_gt{ 'num1; 'num2 }
declare int_ge{ 'num1; 'num2 }

(*
 * Lists.
 *)

declare nil
declare cons{ 'elt; 'tail }

(*
 * Integer sets.
 *)

declare interval{ 'left; 'right }
declare intset{ 'interval_list }
declare rawintset[precision:n, sign:s]{ 'interval_list }
declare member{ 'num; 'set }

declare intset_max
declare enum_max
declare rawintset_max[precision:n, sign:s]

(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*
 * Booleans.
 *)

topval reduce_and : conv
topval reduce_or : conv
topval reduce_not : conv
topval reduce_ifthenelse_true : conv
topval reduce_ifthenelse_false : conv

(*
 * Integers.
 *)

topval reduce_add : conv
topval reduce_sub : conv
topval reduce_mul : conv
topval reduce_div : conv
topval reduce_rem : conv
topval reduce_minus : conv
topval reduce_numeral : conv

topval reduce_int_eq : conv
topval reduce_int_neq : conv
topval reduce_int_lt : conv
topval reduce_int_le : conv
topval reduce_int_gt : conv
topval reduce_int_ge : conv

(*
 * Lists.
 *)

topval reduce_member_interval : conv
topval reduce_member_intset_ind : conv
topval reduce_member_intset_base : conv
topval reduce_member_rawintset_ind : conv
topval reduce_member_rawintset_base : conv

(*
 * Integer sets.
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
