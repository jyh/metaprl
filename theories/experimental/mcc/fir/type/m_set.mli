(*
 * Sets of intervals.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2002 Jason Hickey, Caltech
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
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends M_prec
extends M_int
extends M_rawint

open Refiner.Refiner.TermType

open Fir
open Fir_set

(*
 * An interval has two bounds, and a set is just
 * a list of intervals.
 *)
declare Closed{'i}
declare Open{'i}
declare interval{'lower; 'upper}

(*
 * The intervals are in a list.
 *)
declare IntSet{'intervals}
declare RawIntSet[precision:n, signed:t]{'intervals}

(*
 * Term conversions.
 *)
val dest_set : term -> set
val make_set : set -> term

val dest_int_set : term -> IntSet.t
val make_int_set : IntSet.t -> term

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
