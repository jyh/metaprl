(*
 * The Mfir_int module implements integers for the FIR theory.
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

open Tactic_type.Conversionals


(**************************************************************************
 * Declarations.
 **************************************************************************)

(*
 * Numbers.
 *)

declare number[i:n]


(*
 * Operations.
 *)

declare add{ 'num1; 'num2 }
declare sub{ 'num1; 'num2 }
declare mul{ 'num1; 'num2 }
declare div{ 'num1; 'num2 }
declare rem{ 'num1; 'num2 }
declare minus{ 'num }
declare int_min{ 'num1; 'num2 }
declare int_max{ 'num1; 'num2 }

declare int_eq{ 'num1; 'num2 }
declare int_neq{ 'num1; 'num2 }
declare int_lt{ 'num1; 'num2 }
declare int_le{ 'num1; 'num2 }
declare int_gt{ 'num1; 'num2 }
declare int_ge{ 'num1; 'num2 }


(**************************************************************************
 * Rewrites.
 **************************************************************************)

topval reduce_add : conv
topval reduce_sub : conv
topval reduce_mul : conv
topval reduce_div : conv
topval reduce_rem : conv
topval reduce_minus : conv
topval reduce_int_min : conv
topval reduce_int_max : conv

topval reduce_int_eq : conv
topval reduce_int_neq : conv
topval reduce_int_lt : conv
topval reduce_int_le : conv
topval reduce_int_gt : conv
topval reduce_int_ge : conv
