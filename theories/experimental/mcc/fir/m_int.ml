(*
 * Raw integers.
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
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError

open M_prec

(*
 * For now, use a numeric representation.
 *)
declare int[value:n]

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

(*
 * Display.
 *)
dform int_df : int[i:n] =
   slot[i:n]

dform int_uminus_df : parens :: "prec"[prec_uminus] :: int_uminus{'i} =
   `"-" slot{'i}

dform int_lnot_df : parens :: "prec"[prec_uminus] :: int_lnot{'i} =
   `"~" slot{'i}

dform int_plus_df : parens :: "prec"[prec_add] :: int_plus{'i1; 'i2} =
   slot{'i1} hspace `"+ " slot{'i2}

dform int_minus_df : parens :: "prec"[prec_add] :: int_minus{'i1; 'i2} =
   slot{'i1} hspace `"- " slot{'i2}

dform int_mul_df : parens :: "prec"[prec_mul] :: int_mul{'i1; 'i2} =
   slot{'i1} hspace `"* " slot{'i2}

dform int_div_df : parens :: "prec"[prec_mul] :: int_div{'i1; 'i2} =
   slot{'i1} hspace `"/ " slot{'i2}

dform int_rem_df : parens :: "prec"[prec_mul] :: int_rem{'i1; 'i2} =
   slot{'i1} hspace bf["rem "] slot{'i2}

dform int_max_df : parens :: "prec"[prec_apply] :: int_max{'i1; 'i2} =
   bf["max"] `"(" slot{'i1} `", " slot{'i2} `")"

dform int_min_df : parens :: "prec"[prec_apply] :: int_min{'i1; 'i2} =
   bf["min"] `"(" slot{'i1} `", " slot{'i2} `")"

dform int_sl_df : parens :: "prec"[prec_shift] :: int_sl{'i1; 'i2} =
   slot{'i1} hspace `"<< " slot{'i2}

dform int_sr_df : parens :: "prec"[prec_shift] :: int_sr{'i1; 'i2} =
   slot{'i1} hspace `">> " slot{'i2}

dform int_and_df : parens :: "prec"[prec_and] :: int_and{'i1; 'i2} =
   slot{'i1} hspace `"& " slot{'i2}

dform int_or_df : parens :: "prec"[prec_and] :: int_or{'i1; 'i2} =
   slot{'i1} hspace `"| " slot{'i2}

dform int_xor_df : parens :: "prec"[prec_and] :: int_xor{'i1; 'i2} =
   slot{'i1} hspace `"^ " slot{'i2}

dform int_if_eq_df : parens :: "prec"[prec_if] :: int_if_eq{'i1; 'i2; 'e1; 'e2} =
   szone pushm[0] pushm[3] bf["if "] slot{'i1} bf[" = "] slot{'i2} bf["then"]
   hspace slot{'e1}
   popm hspace pushm[3] bf["else"]
   hspace slot{'e2}
   popm popm ezone

dform int_if_lt_df : parens :: "prec"[prec_if] :: int_if_lt{'i1; 'i2; 'e1; 'e2} =
   szone pushm[0] pushm[3] bf["if "] slot{'i1} bf[" < "] slot{'i2} bf["then"]
   hspace slot{'e1}
   popm hspace pushm[3] bf["else"]
   hspace slot{'e2}
   popm popm ezone

(*
 * Conversion to terms.
 *)
let int_term = << int[0:n] >>
let int_opname = opname_of_term int_term

let mk_int_term i =
   mk_number_term int_opname (Mp_num.num_of_int i)

let dest_int_term t =
   Mp_num.int_of_num (dest_number_term int_opname t)

(*
 * Arithmetic operations.
 *)
let unary_arith op goal =
   let i = one_subterm goal in
      mk_int_term (op (dest_int_term i))

let binary_arith op goal =
   let i1, i2 = two_subterms goal in
      mk_int_term (op (dest_int_term i1) (dest_int_term i2))

let check_zero op a b =
   if b = 0 then
      raise (RefineError ("M_int.arith", StringError "division by zero"))
   else
      op a b

(*
 * Actual reductions.
 *)
ml_rw reduce_int_uminus : ('goal : int_uminus{'i}) =
   unary_arith (~-) goal

ml_rw reduce_int_lnot : ('goal : int_lnot{'i}) =
   unary_arith (lnot) goal

ml_rw reduce_int_plus : ('goal : int_plus{'i1; 'i2}) =
   binary_arith (+) goal

ml_rw reduce_int_minus : ('goal : int_minus{'i1; 'i2}) =
   binary_arith (-) goal

ml_rw reduce_int_mul : ('goal : int_mul{'i1; 'i2}) =
   binary_arith ( * ) goal

ml_rw reduce_int_div : ('goal : int_div{'i1; 'i2}) =
   binary_arith (check_zero (/)) goal

ml_rw reduce_int_rem  : ('goal : int_rem{'i1; 'i2}) =
   binary_arith (check_zero (mod)) goal

ml_rw reduce_int_min  : ('goal : int_min{'i1; 'i2}) =
   binary_arith min goal

ml_rw reduce_int_max  : ('goal : int_max{'i1; 'i2}) =
   binary_arith max goal

ml_rw reduce_int_sl  : ('goal : int_sl{'i1; 'i2}) =
   binary_arith (lsl) goal

ml_rw reduce_int_sr  : ('goal : int_sr{'i1; 'i2}) =
   binary_arith (asr) goal

ml_rw reduce_int_and  : ('goal : int_and{'i1; 'i2}) =
   binary_arith (land) goal

ml_rw reduce_int_or  : ('goal : int_or{'i1; 'i2}) =
   binary_arith (lor) goal

ml_rw reduce_int_xor  : ('goal : int_xor{'i1; 'i2}) =
   binary_arith (lxor) goal

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
