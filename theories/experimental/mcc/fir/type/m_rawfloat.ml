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
 * For now, use the string representation.
 *)
declare rawfloat[precision:n, value:s]

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
 * Display.
 *)
declare precision[p:n]

dform precision_df : precision[p:n] =
   slot[p:n]

dform rawfloat_df : rawfloat[p:n, v:s] =
   slot[v:s] `":" precision[p:n]

dform rawfloat_uminus_df : parens :: "prec"[prec_uminus] :: rawfloat_uminus{'i} =
   `"-" slot{'i}

dform rawfloat_of_rawfloat_df : parens :: "prec"[prec_coerce] :: rawfloat_of_rawfloat[p:n]{'i} =
   `"(rawfloat-of-rawfloat " precision[p:n] `") " slot{'i}

dform rawfloat_of_int_df : parens :: "prec"[prec_coerce] :: rawfloat_of_int[p:n]{'i} =
   `"(rawfloat-of-int " precision[p:n] `") " slot{'i}

dform rawfloat_plus_df : parens :: "prec"[prec_add] :: rawfloat_plus{'i1; 'i2} =
   slot{'i1} hspace `"+ " slot{'i2}

dform rawfloat_minus_df : parens :: "prec"[prec_add] :: rawfloat_minus{'i1; 'i2} =
   slot{'i1} hspace `"- " slot{'i2}

dform rawfloat_mul_df : parens :: "prec"[prec_mul] :: rawfloat_mul{'i1; 'i2} =
   slot{'i1} hspace `"* " slot{'i2}

dform rawfloat_div_df : parens :: "prec"[prec_mul] :: rawfloat_div{'i1; 'i2} =
   slot{'i1} hspace `"/ " slot{'i2}

dform rawfloat_rem_df : parens :: "prec"[prec_mul] :: rawfloat_rem{'i1; 'i2} =
   slot{'i1} hspace bf["rem "] slot{'i2}

dform rawfloat_max_df : parens :: "prec"[prec_apply] :: rawfloat_max{'i1; 'i2} =
   bf["max"] `"(" slot{'i1} `", " slot{'i2} `")"

dform rawfloat_min_df : parens :: "prec"[prec_apply] :: rawfloat_min{'i1; 'i2} =
   bf["min"] `"(" slot{'i1} `", " slot{'i2} `")"

dform rawfloat_if_eq_df : parens :: "prec"[prec_if] :: rawfloat_if_eq{'i1; 'i2; 'e1; 'e2} =
   szone pushm[0] pushm[3] bf["if "] slot{'i1} bf[" = "] slot{'i2} bf["then"]
   hspace slot{'e1}
   popm hspace pushm[3] bf["else"]
   hspace slot{'e2}
   popm popm ezone

dform rawfloat_if_lt_df : parens :: "prec"[prec_if] :: rawfloat_if_lt{'i1; 'i2; 'e1; 'e2} =
   szone pushm[0] pushm[3] bf["if "] slot{'i1} bf[" < "] slot{'i2} bf["then"]
   hspace slot{'e1}
   popm hspace pushm[3] bf["else"]
   hspace slot{'e2}
   popm popm ezone

(************************************************************************
 * Term conversions.
 *)

(*
 * Precisions.
 *)
let rawfloat_precision_of_num p =
   match Mp_num.int_of_num p with
      32 -> Lm_rawfloat.Single
    | 64 -> Lm_rawfloat.Double
    | 80 -> Lm_rawfloat.LongDouble
    | i -> raise (RefineError ("dest_rawfloat_precision", StringIntError ("bad precision", i)))

(*
 * Make a precision.
 *)
let num_of_rawfloat_precision p =
   let i =
      match p with
         Lm_rawfloat.Single -> 32
       | Lm_rawfloat.Double -> 64
       | Lm_rawfloat.LongDouble -> 80
   in
      Mp_num.num_of_int i

(*
 * Conversion to terms.
 *)
let term_rawfloat = << rawfloat[64:n, "0":s] >>
let opname_rawfloat = opname_of_term term_rawfloat

let dest_rawfloat t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = List.map dest_param params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [Number p; String v], []
         when Opname.eq op opname_rawfloat ->
            let p = rawfloat_precision_of_num p in
               Lm_rawfloat.of_string p v
       | _ ->
            raise (RefineError ("dest_rawfloat", StringTermError ("not a rawfloat", t)))


let make_rawfloat i =
   let p = num_of_rawfloat_precision (Lm_rawfloat.precision i) in
   let v = Lm_rawfloat.to_string i in
   let params =
      [make_param (Number  p);
       make_param (String v)]
   in
   let op = mk_op opname_rawfloat params in
      mk_term op []

(************************************************************************
 * Arithmetic.
 *)

(*
 * Arithmetic operations.
 *)
let unary_arith op goal =
   let i = one_subterm goal in
      make_rawfloat (op (dest_rawfloat i))

let binary_arith op goal =
   let i1, i2 = two_subterms goal in
      make_rawfloat (op (dest_rawfloat i1) (dest_rawfloat i2))

let check_zero op a b =
   if Lm_rawfloat.is_zero b then
      raise (RefineError ("M_rawfloat.arith", StringError "division by zero"))
   else
      op a b

(*
 * Actual reductions.
 *)
ml_rw reduce_rawfloat_uminus : ('goal : rawfloat_uminus{'i}) =
   unary_arith Lm_rawfloat.uminus goal

ml_rw reduce_rawfloat_plus : ('goal : rawfloat_plus{'i1; 'i2}) =
   binary_arith Lm_rawfloat.add goal

ml_rw reduce_rawfloat_minus : ('goal : rawfloat_minus{'i1; 'i2}) =
   binary_arith Lm_rawfloat.sub goal

ml_rw reduce_rawfloat_mul : ('goal : rawfloat_mul{'i1; 'i2}) =
   binary_arith Lm_rawfloat.mul goal

ml_rw reduce_rawfloat_div : ('goal : rawfloat_div{'i1; 'i2}) =
   binary_arith (check_zero Lm_rawfloat.div) goal

ml_rw reduce_rawfloat_rem  : ('goal : rawfloat_rem{'i1; 'i2}) =
   binary_arith (check_zero Lm_rawfloat.rem) goal

ml_rw reduce_rawfloat_min  : ('goal : rawfloat_min{'i1; 'i2}) =
   binary_arith Lm_rawfloat.min goal

ml_rw reduce_rawfloat_max  : ('goal : rawfloat_max{'i1; 'i2}) =
   binary_arith Lm_rawfloat.max goal

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
