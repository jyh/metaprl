(*
 * Integers with various precisions.
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

open Lm_rawfloat

(*
 * For now, use the string representation.
 *)
declare rawfloat[precision:n, value:s]

(*
 * For display purposes.
 *)
declare precision[p:n]

(*
 * Arithmetic.
 *)
declare rawfloat_uminus{'i}

declare rawfloat_of_rawfloat[p:n]{'i}
declare rawfloat_of_int[p:n]{'i}

declare rawfloat_plus{'i1; 'i2}
declare rawfloat_minus{'i1; 'i2}
declare rawfloat_mul{'i1; 'i2}
declare rawfloat_div{'i1; 'i2}
declare rawfloat_rem{'i1; 'i2}
declare rawfloat_max{'i1; 'i2}
declare rawfloat_min{'i1; 'i2}

declare rawfloat_if_eq{'i1; 'i2; 'e1; 'e2}
declare rawfloat_if_lt{'i1; 'i2; 'e1; 'e2}

(*
 * Term conversions.
 *)
val rawfloat_precision_of_num : Lm_num.num -> float_precision
val dest_rawfloat : term -> rawfloat

val num_of_rawfloat_precision : float_precision -> Lm_num.num
val make_rawfloat : rawfloat -> term

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
