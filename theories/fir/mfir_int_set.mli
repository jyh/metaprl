(*
 * The Mfir_int_set module defines integer sets and operations on them.
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
declare intset[precision:n, sign:s]{ 'interval_list }


(*
 * Set operations.
 *)

declare member{ 'num; 's }
declare normalize{ 'set }
declare "subset"{ 'set1; 'set2 }
declare set_eq{ 'set1; 'set2 }
declare union{ 'set1; 'set2 }


(*
 * Constants.
 *)

declare intset_max[precision:n, sign:s]
declare enum_max


(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*
 * Set operations.
 *)

topval reduce_member : conv
topval reduce_normalize : conv
topval reduce_subset : conv
topval reduce_set_eq : conv
topval reduce_union : conv


(*
 * Constants.
 *)

topval reduce_intset_max : conv
topval reduce_enum_max : conv
