(*
 * Operations on 31-bit integers.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
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

open Refiner.Refiner.TermType

(*
 * For now, use a numeric representation.
 *)
declare int[value:n]

(*
 * Term conversions.
 *)
val dest_int : term -> int
val make_int : int -> term

(*
 * Arithmetic.
 *)
declare int_uminus{'i}
declare int_lnot{'i}
declare int_bitfield[off:n, len:n]{'i}

declare int_plus{'i1; 'i2}
declare int_minus{'i1; 'i2}
declare int_mul{'i1; 'i2}
declare int_div{'i1; 'i2}
declare int_rem{'i1; 'i2}
declare int_max{'i1; 'i2}
declare int_min{'i1; 'i2}

declare int_sl{'i1; 'i2}
declare int_sr{'i1; 'i2}
declare int_and{'i1; 'i2}
declare int_or{'i1; 'i2}
declare int_xor{'i1; 'i2}

declare int_if_eq{'i1; 'i2; 'e1; 'e2}
declare int_if_lt{'i1; 'i2; 'e1; 'e2}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
