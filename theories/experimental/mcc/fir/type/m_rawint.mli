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

open Lm_rawint

(*
 * For now, use the string representation.
 *)
declare rawint[precision:n, signed:t, value:s]

(*
 * Term conversions.
 *)
val rawint_precision_of_num : Mp_num.num -> int_precision
val boolean_of_string : string -> bool
val dest_rawint : term -> rawint

val num_of_rawint_precision : int_precision -> Mp_num.num
val string_of_boolean : bool -> string
val make_rawint : rawint -> term


(*
 * Arithmetic.
 *)
declare rawint_uminus{'i}
declare rawint_lnot{'i}
declare rawint_bitfield[off:n, len:n]{'i}

declare rawint_of_rawint[p:n, s:t]{'i}
declare rawint_of_int[p:n, s:t]{'i}

declare rawint_plus{'i1; 'i2}
declare rawint_minus{'i1; 'i2}
declare rawint_mul{'i1; 'i2}
declare rawint_div{'i1; 'i2}
declare rawint_rem{'i1; 'i2}
declare rawint_max{'i1; 'i2}
declare rawint_min{'i1; 'i2}

declare rawint_sl{'i1; 'i2}
declare rawint_sr{'i1; 'i2}
declare rawint_and{'i1; 'i2}
declare rawint_or{'i1; 'i2}
declare rawint_xor{'i1; 'i2}

declare rawint_if_eq{'i1; 'i2; 'e1; 'e2}
declare rawint_if_lt{'i1; 'i2; 'e1; 'e2}

(*
 * For display purposes.
 *)
declare precision[p:n, s:t]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
