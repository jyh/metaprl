(*
 * Basic operations for converting MCC FIR expressions
 * to/from MetaPRL terms.
 *
 * ----------------------------------------------------------------
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

(* Open MCC ML namespaces. *)

open Interval_set
open Rawint
open Rawfloat
open Symbol
open Fir_set
open Fir

(* Open MetaPRL ML namespaces. *)

open Mp_num
open Refiner.Refiner.Term
open Refiner.Refiner.RefineError
open Mfir_termOp
open Mfir_connect_base
open Mfir_connect_ty


(**************************************************************************
 * Convert to and from unop.
 **************************************************************************)

let term_of_unop op =
   match op with
      NotEnumOp i ->    mk_notEnumOp_term (num_of_int i)

    | UMinusIntOp ->    uminusIntOp_term
    | NotIntOp ->       notIntOp_term
    | AbsIntOp ->       absIntOp_term

    | RawBitFieldOp (pre, sign, i1, i2) ->
         mk_rawBitFieldOp_term   (num_of_int_precision pre)
                                 (string_of_int_signed sign)
                                 (number_term_of_int i1)
                                 (number_term_of_int i2)

    | UMinusFloatOp pre ->
         mk_uminusFloatOp_term   (num_of_float_precision pre)
    | AbsFloatOp pre ->
         mk_absFloatOp_term      (num_of_float_precision pre)
    | SinFloatOp pre ->
         mk_sinFloatOp_term      (num_of_float_precision pre)
    | CosFloatOp pre ->
         mk_cosFloatOp_term      (num_of_float_precision pre)
    | TanFloatOp pre ->
         mk_tanFloatOp_term      (num_of_float_precision pre)
    | ASinFloatOp pre ->
         mk_asinFloatOp_term     (num_of_float_precision pre)
    | ACosFloatOp pre ->
         mk_acosFloatOp_term     (num_of_float_precision pre)
    | ATanFloatOp pre ->
         mk_atanFloatOp_term     (num_of_float_precision pre)
    | SinHFloatOp pre ->
         mk_sinhFloatOp_term     (num_of_float_precision pre)
    | CosHFloatOp pre ->
         mk_coshFloatOp_term     (num_of_float_precision pre)
    | TanHFloatOp pre ->
         mk_tanhFloatOp_term     (num_of_float_precision pre)
    | ExpFloatOp pre ->
         mk_expFloatOp_term      (num_of_float_precision pre)
    | LogFloatOp pre ->
         mk_logFloatOp_term      (num_of_float_precision pre)
    | Log10FloatOp pre ->
         mk_log10FloatOp_term    (num_of_float_precision pre)
    | SqrtFloatOp pre ->
         mk_sqrtFloatOp_term     (num_of_float_precision pre)
    | CeilFloatOp pre ->
         mk_ceilFloatOp_term     (num_of_float_precision pre)
    | FloorFloatOp pre ->
         mk_floorFloatOp_term    (num_of_float_precision pre)

    | IntOfFloatOp pre ->
         mk_intOfFloatOp_term    (num_of_float_precision pre)
    | IntOfRawIntOp (pre, sign) ->
         mk_intOfRawIntOp_term   (num_of_int_precision pre)
                                 (string_of_int_signed sign)

    | FloatOfIntOp pre ->
         mk_floatOfIntOp_term    (num_of_float_precision pre)
    | FloatOfFloatOp (dpre, spre) ->
         mk_floatOfFloatOp_term  (num_of_float_precision dpre)
                                 (num_of_float_precision spre)
    | FloatOfRawIntOp (fpre, ipre, sign) ->
         mk_floatOfRawIntOp_term (num_of_float_precision fpre)
                                 (num_of_int_precision ipre)
                                 (string_of_int_signed sign)

    | RawIntOfIntOp (pre, sign) ->
         mk_rawIntOfIntOp_term   (num_of_int_precision pre)
                                 (string_of_int_signed sign)
    | RawIntOfEnumOp (pre, sign, i) ->
         mk_rawIntOfEnumOp_term  (num_of_int_precision pre)
                                 (string_of_int_signed sign)
                                 (num_of_int i)
    | RawIntOfFloatOp (ipre, sign, fpre) ->
         mk_rawIntOfFloatOp_term (num_of_int_precision ipre)
                                 (string_of_int_signed sign)
                                 (num_of_float_precision fpre)
    | RawIntOfRawIntOp (dpre, dsign, spre, ssign) ->
         mk_rawIntOfRawIntOp_term   (num_of_int_precision dpre)
                                    (string_of_int_signed dsign)
                                    (num_of_int_precision spre)
                                    (string_of_int_signed ssign)

    | RawIntOfPointerOp (pre, sign) ->
         mk_rawIntOfPointerOp_term  (num_of_int_precision pre)
                                    (string_of_int_signed sign)
    | PointerOfRawIntOp (pre, sign) ->
         mk_pointerOfRawIntOp_term  (num_of_int_precision pre)
                                    (string_of_int_signed sign)

    | DTupleOfDTupleOp (tv, mtyl) ->
         mk_dtupleOfDTupleOp_term   (term_of_symbol tv)
                                    (term_of_list term_of_mutable_ty mtyl)
    | UnionOfUnionOp (tv, tyl, set1, set2) ->
         mk_unionOfUnionOp_term     (term_of_symbol tv)
                                    (term_of_list term_of_ty tyl)
                                    (term_of_int_set set1)
                                    (term_of_int_set set2)
    | RawDataOfFrameOp (tv, tyl) ->
         mk_rawDataOfFrameOp_term   (term_of_symbol tv)
                                    (term_of_list term_of_ty tyl)

    | _ ->
         raise (Invalid_argument "term_of_unop: unknown unop")


let unop_of_term t =
   if is_notEnumOp_term t then
      let i = dest_notEnumOp_term t in
         NotEnumOp (int_of_num i)

   else if is_uminusIntOp_term t then
      UMinusIntOp
   else if is_notIntOp_term t then
      NotIntOp
   else if is_absIntOp_term t then
      AbsIntOp

   else if is_rawBitFieldOp_term t then
      let pre, sign, i1, i2 = dest_rawBitFieldOp_term t in
         RawBitFieldOp  (int_precision_of_num pre,
                         int_signed_of_string sign,
                         int_of_number_term i1,
                         int_of_number_term i2)

   else if is_uminusFloatOp_term t then
      UMinusFloatOp  (float_precision_of_num (dest_uminusFloatOp_term t))
   else if is_absFloatOp_term t then
      AbsFloatOp     (float_precision_of_num (dest_absFloatOp_term t))
   else if is_sinFloatOp_term t then
      SinFloatOp     (float_precision_of_num (dest_sinFloatOp_term t))
   else if is_cosFloatOp_term t then
      CosFloatOp     (float_precision_of_num (dest_cosFloatOp_term t))
   else if is_tanFloatOp_term t then
      TanFloatOp     (float_precision_of_num (dest_tanFloatOp_term t))
   else if is_asinFloatOp_term t then
      ASinFloatOp    (float_precision_of_num (dest_asinFloatOp_term t))
   else if is_acosFloatOp_term t then
      ACosFloatOp    (float_precision_of_num (dest_acosFloatOp_term t))
   else if is_atanFloatOp_term t then
      ATanFloatOp    (float_precision_of_num (dest_atanFloatOp_term t))
   else if is_sinhFloatOp_term t then
      SinHFloatOp    (float_precision_of_num (dest_sinhFloatOp_term t))
   else if is_coshFloatOp_term t then
      CosHFloatOp    (float_precision_of_num (dest_coshFloatOp_term t))
   else if is_tanhFloatOp_term t then
      TanHFloatOp    (float_precision_of_num (dest_tanhFloatOp_term t))
   else if is_expFloatOp_term t then
      ExpFloatOp     (float_precision_of_num (dest_expFloatOp_term t))
   else if is_logFloatOp_term t then
      LogFloatOp     (float_precision_of_num (dest_logFloatOp_term t))
   else if is_log10FloatOp_term t then
      Log10FloatOp   (float_precision_of_num (dest_log10FloatOp_term t))
   else if is_sqrtFloatOp_term t then
      SqrtFloatOp    (float_precision_of_num (dest_sqrtFloatOp_term t))
   else if is_ceilFloatOp_term t then
      CeilFloatOp    (float_precision_of_num (dest_ceilFloatOp_term t))
   else if is_floorFloatOp_term t then
      FloorFloatOp   (float_precision_of_num (dest_floorFloatOp_term t))

   else if is_intOfFloatOp_term t then
      IntOfFloatOp   (float_precision_of_num (dest_intOfFloatOp_term t))
   else if is_intOfRawIntOp_term t then
      let pre, sign = dest_intOfRawIntOp_term t in
         IntOfRawIntOp  ((int_precision_of_num pre),
                         (int_signed_of_string sign))

   else if is_floatOfIntOp_term t then
      FloatOfIntOp   (float_precision_of_num (dest_floatOfIntOp_term t))
   else if is_floatOfFloatOp_term t then
      let dpre, spre = dest_floatOfFloatOp_term t in
         FloatOfFloatOp ((float_precision_of_num dpre),
                         (float_precision_of_num spre))
   else if is_floatOfRawIntOp_term t then
      let fpre, ipre, sign = dest_floatOfRawIntOp_term t in
         FloatOfRawIntOp   ((float_precision_of_num fpre),
                            (int_precision_of_num ipre),
                            (int_signed_of_string sign))

   else if is_rawIntOfIntOp_term t then
      let pre, sign = dest_rawIntOfIntOp_term t in
         RawIntOfIntOp     ((int_precision_of_num pre),
                            (int_signed_of_string sign))
   else if is_rawIntOfEnumOp_term t then
      let pre, sign, i = dest_rawIntOfEnumOp_term t in
         RawIntOfEnumOp    ((int_precision_of_num pre),
                            (int_signed_of_string sign),
                            (int_of_num i))
   else if is_rawIntOfFloatOp_term t then
      let ipre, sign, fpre = dest_rawIntOfFloatOp_term t in
         RawIntOfFloatOp   ((int_precision_of_num ipre),
                            (int_signed_of_string sign),
                            (float_precision_of_num fpre))
   else if is_rawIntOfRawIntOp_term t then
      let dpre, dsign, spre, ssign = dest_rawIntOfRawIntOp_term t in
         RawIntOfRawIntOp  ((int_precision_of_num dpre),
                            (int_signed_of_string dsign),
                            (int_precision_of_num spre),
                            (int_signed_of_string ssign))

   else if is_rawIntOfPointerOp_term t then
      let pre, sign = dest_rawIntOfPointerOp_term t in
         RawIntOfPointerOp ((int_precision_of_num pre),
                            (int_signed_of_string sign))
   else if is_pointerOfRawIntOp_term t then
      let pre, sign = dest_pointerOfRawIntOp_term t in
         PointerOfRawIntOp ((int_precision_of_num pre),
                            (int_signed_of_string sign))

   else if is_dtupleOfDTupleOp_term t then
      let tv, mtyl = dest_dtupleOfDTupleOp_term t in
         DTupleOfDTupleOp  ((symbol_of_term tv),
                            (list_of_term mutable_ty_of_term mtyl))
   else if is_unionOfUnionOp_term t then
      let tv, tyl, set1, set2 = dest_unionOfUnionOp_term t in
         UnionOfUnionOp    ((symbol_of_term tv),
                            (list_of_term ty_of_term tyl),
                            (int_set_of_term set1),
                            (int_set_of_term set2))
   else if is_rawDataOfFrameOp_term t then
      let tv, tyl = dest_rawDataOfFrameOp_term t in
         RawDataOfFrameOp  ((symbol_of_term tv),
                            (list_of_term ty_of_term tyl))

   else
      report_error "unop_of_term" t


(**************************************************************************
 * Convert to and from binop.
 **************************************************************************)

let term_of_binop op =
   match op with

      AndEnumOp i -> mk_andEnumOp_term (num_of_int i)
    | OrEnumOp i ->  mk_orEnumOp_term  (num_of_int i)
    | XorEnumOp i -> mk_xorEnumOp_term (num_of_int i)

    | PlusIntOp ->   plusIntOp_term
    | MinusIntOp ->  minusIntOp_term
    | MulIntOp ->    mulIntOp_term
    | DivIntOp ->    divIntOp_term
    | RemIntOp ->    remIntOp_term
    | LslIntOp ->    lslIntOp_term
    | LsrIntOp ->    lsrIntOp_term
    | AsrIntOp ->    asrIntOp_term
    | AndIntOp ->    andIntOp_term
    | OrIntOp ->     orIntOp_term
    | XorIntOp ->    xorIntOp_term
    | MaxIntOp ->    maxIntOp_term
    | MinIntOp ->    minIntOp_term

    | EqIntOp ->     eqIntOp_term
    | NeqIntOp ->    neqIntOp_term
    | LtIntOp ->     ltIntOp_term
    | LeIntOp ->     leIntOp_term
    | GtIntOp ->     gtIntOp_term
    | GeIntOp ->     geIntOp_term
    | CmpIntOp ->    cmpIntOp_term

    | PlusRawIntOp (p, s) ->
         mk_plusRawIntOp_term (num_of_int_precision p) (string_of_int_signed s)
    | MinusRawIntOp (p, s) ->
         mk_minusRawIntOp_term (num_of_int_precision p) (string_of_int_signed s)
    | MulRawIntOp (p, s) ->
         mk_mulRawIntOp_term  (num_of_int_precision p) (string_of_int_signed s)
    | DivRawIntOp (p, s) ->
         mk_divRawIntOp_term  (num_of_int_precision p) (string_of_int_signed s)
    | RemRawIntOp (p, s) ->
         mk_remRawIntOp_term  (num_of_int_precision p) (string_of_int_signed s)
    | SlRawIntOp (p, s) ->
         mk_slRawIntOp_term   (num_of_int_precision p) (string_of_int_signed s)
    | SrRawIntOp (p, s) ->
         mk_srRawIntOp_term   (num_of_int_precision p) (string_of_int_signed s)
    | AndRawIntOp (p, s) ->
         mk_andRawIntOp_term  (num_of_int_precision p) (string_of_int_signed s)
    | OrRawIntOp (p, s) ->
         mk_orRawIntOp_term   (num_of_int_precision p) (string_of_int_signed s)
    | XorRawIntOp (p, s) ->
         mk_xorRawIntOp_term  (num_of_int_precision p) (string_of_int_signed s)
    | MaxRawIntOp (p, s) ->
         mk_maxRawIntOp_term  (num_of_int_precision p) (string_of_int_signed s)
    | MinRawIntOp (p, s) ->
         mk_minRawIntOp_term  (num_of_int_precision p) (string_of_int_signed s)

    | RawSetBitFieldOp (p, s, i1, i2) ->
         mk_rawSetBitFieldOp_term (num_of_int_precision p)
                                  (string_of_int_signed s)
                                  (number_term_of_int i1)
                                  (number_term_of_int i2)

    | EqRawIntOp (p, s) ->
         mk_eqRawIntOp_term   (num_of_int_precision p) (string_of_int_signed s)
    | NeqRawIntOp (p, s) ->
         mk_neqRawIntOp_term  (num_of_int_precision p) (string_of_int_signed s)
    | LtRawIntOp (p, s) ->
         mk_ltRawIntOp_term   (num_of_int_precision p) (string_of_int_signed s)
    | LeRawIntOp (p, s) ->
         mk_leRawIntOp_term   (num_of_int_precision p) (string_of_int_signed s)
    | GtRawIntOp (p, s) ->
         mk_gtRawIntOp_term   (num_of_int_precision p) (string_of_int_signed s)
    | GeRawIntOp (p,  s) ->
         mk_geRawIntOp_term   (num_of_int_precision p) (string_of_int_signed s)
    | CmpRawIntOp (p, s) ->
         mk_cmpRawIntOp_term  (num_of_int_precision p) (string_of_int_signed s)

    | PlusFloatOp p ->  mk_plusFloatOp_term  (num_of_float_precision p)
    | MinusFloatOp p -> mk_minusFloatOp_term (num_of_float_precision p)
    | MulFloatOp p ->   mk_mulFloatOp_term   (num_of_float_precision p)
    | DivFloatOp p ->   mk_divFloatOp_term   (num_of_float_precision p)
    | RemFloatOp p ->   mk_remFloatOp_term   (num_of_float_precision p)
    | MaxFloatOp p ->   mk_maxFloatOp_term   (num_of_float_precision p)
    | MinFloatOp p ->   mk_minFloatOp_term   (num_of_float_precision p)

    | EqFloatOp p ->    mk_eqFloatOp_term    (num_of_float_precision p)
    | NeqFloatOp p ->   mk_neqFloatOp_term   (num_of_float_precision p)
    | LtFloatOp p ->    mk_ltFloatOp_term    (num_of_float_precision p)
    | LeFloatOp p ->    mk_leFloatOp_term    (num_of_float_precision p)
    | GtFloatOp p ->    mk_gtFloatOp_term    (num_of_float_precision p)
    | GeFloatOp p ->    mk_geFloatOp_term    (num_of_float_precision p)
    | CmpFloatOp p ->   mk_cmpFloatOp_term   (num_of_float_precision p)

    | ATan2FloatOp p ->
         mk_atan2FloatOp_term    (num_of_float_precision p)
    | PowerFloatOp p ->
         mk_powerFloatOp_term    (num_of_float_precision p)
    | LdExpFloatIntOp p ->
         mk_ldExpFloatIntOp_term (num_of_float_precision p)

    | EqEqOp ty ->
         mk_eqEqOp_term       (term_of_ty ty)
    | NeqEqOp ty ->
         mk_neqEqOp_term      (term_of_ty ty)

    | _ ->
         raise (Invalid_argument "term_of_binop: unknown binop")


let binop_of_term t =
   if is_andEnumOp_term t then
      AndEnumOp   (int_of_num (dest_andEnumOp_term t))
   else if is_orEnumOp_term t then
      OrEnumOp    (int_of_num (dest_orEnumOp_term t))
   else if is_xorEnumOp_term t then
      XorEnumOp   (int_of_num (dest_xorEnumOp_term t))

   else if is_plusIntOp_term t then    PlusIntOp
   else if is_minusIntOp_term t then   MinusIntOp
   else if is_mulIntOp_term t then     MulIntOp
   else if is_divIntOp_term t then     DivIntOp
   else if is_remIntOp_term t then     RemIntOp
   else if is_lslIntOp_term t then     LslIntOp
   else if is_lsrIntOp_term t then     LsrIntOp
   else if is_asrIntOp_term t then     AsrIntOp
   else if is_andIntOp_term t then     AndIntOp
   else if is_orIntOp_term t then      OrIntOp
   else if is_xorIntOp_term t then     XorIntOp
   else if is_maxIntOp_term t then     MaxIntOp
   else if is_minIntOp_term t then     MinIntOp

   else if is_eqIntOp_term t then      EqIntOp
   else if is_neqIntOp_term t then     NeqIntOp
   else if is_ltIntOp_term t then      LtIntOp
   else if is_leIntOp_term t then      LeIntOp
   else if is_gtIntOp_term t then      GtIntOp
   else if is_geIntOp_term t then      GeIntOp
   else if is_cmpIntOp_term t then     CmpIntOp

   else if is_plusRawIntOp_term t then
      let p, s = dest_plusRawIntOp_term t in
         PlusRawIntOp   (int_precision_of_num p) (int_signed_of_string s)
   else if is_minusRawIntOp_term t then
      let p, s = dest_minusRawIntOp_term t in
         MinusRawIntOp  (int_precision_of_num p) (int_signed_of_string s)
   else if is_mulRawIntOp_term t then
      let p, s = dest_mulRawIntOp_term t in
         MulRawIntOp    (int_precision_of_num p) (int_signed_of_string s)
   else if is_divRawIntOp_term t then
      let p, s = dest_divRawIntOp_term t in
         DivRawIntOp    (int_precision_of_num p) (int_signed_of_string s)
   else if is_remRawIntOp_term t then
      let p, s = dest_remRawIntOp_term t in
         RemRawIntOp    (int_precision_of_num p) (int_signed_of_string s)
   else if is_slRawIntOp_term t then
      let p, s = dest_slRawIntOp_term t in
         SlRawIntOp     (int_precision_of_num p) (int_signed_of_string s)
   else if is_srRawIntOp_term t then
      let p, s = dest_srRawIntOp_term t in
         SrRawIntOp     (int_precision_of_num p) (int_signed_of_string s)
   else if is_andRawIntOp_term t then
      let p, s = dest_andRawIntOp_term t in
         AndRawIntOp    (int_precision_of_num p) (int_signed_of_string s)
   else if is_orRawIntOp_term t then
      let p, s = dest_orRawIntOp_term t in
         OrRawIntOp     (int_precision_of_num p) (int_signed_of_string s)
   else if is_xorRawIntOp_term t then
      let p, s = dest_xorRawIntOp_term t in
         XorRawIntOp    (int_precision_of_num p) (int_signed_of_string s)
   else if is_maxRawIntOp_term t then
      let p, s = dest_maxRawIntOp_term t in
         MaxRawIntOp    (int_precision_of_num p) (int_signed_of_string s)
   else if is_minRawIntOp_term t then
      let p, s = dest_minRawIntOp_term t in
         MinRawIntOp    (int_precision_of_num p) (int_signed_of_string s)

   else if is_rawSetBitFieldOp_term t then
      let p, s, i1, i2 = dest_rawSetBitFieldOp_term t in
         RawSetBitFieldOp (int_precision_of_num p)
                          (int_signed_of_string s)
                          (int_of_number_term i1)
                          (int_of_number_term i2)

   else if is_eqRawIntOp_term t then
      let p, s = dest_eqRawIntOp_term t in
         EqRawIntOp     (int_precision_of_num p) (int_signed_of_string s)
   else if is_neqRawIntOp_term t then
      let p, s = dest_neqRawIntOp_term t in
         NeqRawIntOp    (int_precision_of_num p) (int_signed_of_string s)
   else if is_ltRawIntOp_term t then
      let p, s = dest_ltRawIntOp_term t in
         LtRawIntOp     (int_precision_of_num p) (int_signed_of_string s)
   else if is_leRawIntOp_term t then
      let p, s = dest_leRawIntOp_term t in
         LeRawIntOp     (int_precision_of_num p) (int_signed_of_string s)
   else if is_gtRawIntOp_term t then
      let p, s = dest_gtRawIntOp_term t in
         GtRawIntOp     (int_precision_of_num p) (int_signed_of_string s)
   else if is_geRawIntOp_term t then
      let p, s = dest_geRawIntOp_term t in
         GeRawIntOp     (int_precision_of_num p) (int_signed_of_string s)
   else if is_cmpRawIntOp_term t then
      let p, s = dest_cmpRawIntOp_term t in
         CmpRawIntOp    (int_precision_of_num p) (int_signed_of_string s)

   else if is_plusFloatOp_term t then
      PlusFloatOp    (float_precision_of_num (dest_plusFloatOp_term t))
   else if is_minusFloatOp_term t then
      MinusFloatOp   (float_precision_of_num (dest_minusFloatOp_term t))
   else if is_mulFloatOp_term t then
      MulFloatOp     (float_precision_of_num (dest_mulFloatOp_term t))
   else if is_divFloatOp_term t then
      DivFloatOp     (float_precision_of_num (dest_divFloatOp_term t))
   else if is_remFloatOp_term t then
      RemFloatOp     (float_precision_of_num (dest_remFloatOp_term t))
   else if is_maxFloatOp_term t then
      MaxFloatOp     (float_precision_of_num (dest_maxFloatOp_term t))
   else if is_minFloatOp_term t then
      MinFloatOp     (float_precision_of_num (dest_minFloatOp_term t))

   else if is_eqFloatOp_term t then
      EqFloatOp      (float_precision_of_num (dest_eqFloatOp_term t))
   else if is_neqFloatOp_term t then
      NeqFloatOp     (float_precision_of_num (dest_neqFloatOp_term t))
   else if is_ltFloatOp_term t then
      LtFloatOp      (float_precision_of_num (dest_ltFloatOp_term t))
   else if is_leFloatOp_term t then
      LeFloatOp      (float_precision_of_num (dest_leFloatOp_term t))
   else if is_gtFloatOp_term t then
      GtFloatOp      (float_precision_of_num (dest_gtFloatOp_term t))
   else if is_geFloatOp_term t then
      GeFloatOp      (float_precision_of_num (dest_geFloatOp_term t))
   else if is_cmpFloatOp_term t then
      CmpFloatOp     (float_precision_of_num (dest_cmpFloatOp_term t))

   else if is_atan2FloatOp_term t then
      ATan2FloatOp      (float_precision_of_num (dest_atan2FloatOp_term t))
   else if is_powerFloatOp_term t then
      PowerFloatOp      (float_precision_of_num (dest_powerFloatOp_term t))
   else if is_ldExpFloatIntOp_term t then
      LdExpFloatIntOp   (float_precision_of_num (dest_ldExpFloatIntOp_term t))

   else if is_eqEqOp_term t then
      EqEqOp   (ty_of_term (dest_eqEqOp_term t))
   else if is_neqEqOp_term t then
      NeqEqOp  (ty_of_term (dest_neqEqOp_term t))

   else
      report_error "binop_of_term" t


(**************************************************************************
 * Convert to and from atom.
 **************************************************************************)

let rec term_of_atom a =
   match a with
      AtomNil ty ->
         mk_atomNil_term      (term_of_ty ty)

    | AtomInt i ->
         mk_atomInt_term      (number_term_of_int i)
    | AtomEnum (bound, value) ->
         mk_atomEnum_term     (num_of_int bound)
                              (number_term_of_int value)
    | AtomRawInt r ->
         mk_atomRawInt_term   (num_of_int_precision (Rawint.precision r))
                              (string_of_int_signed (Rawint.signed r))
                              (number_term_of_rawint r)
    | AtomFloat f ->
         raise (Invalid_argument "term_of_atom: floats are not handled")

    | AtomVar v ->
         mk_atomVar_term      (term_of_symbol v)
    | AtomFun v ->
         raise (Invalid_argument "term_of_atom: AtomFun not handled")

    | AtomLabel ((frame, field, subfield), r) ->
         mk_atomLabel_term    (string_of_symbol field)
                              (string_of_symbol subfield)
                              (term_of_symbol frame)
                              (number_term_of_rawint r)
    | AtomSizeof (tvl, r) ->
         mk_atomSizeof_term   (term_of_list term_of_symbol tvl)
                              (number_term_of_rawint r)
    | AtomConst (ty, tv, i) ->
         mk_atomConst_term    (term_of_ty ty)
                              (term_of_symbol tv)
                              (number_term_of_int i)

    | AtomTyApply (a, ty, tyl) ->
         mk_atomTyApply_term  (term_of_atom a)
                              (term_of_ty ty)
                              (term_of_list term_of_ty tyl)
    | AtomTyPack (v, ty, tyl) ->
         mk_atomTyPack_term   (term_of_symbol v)
                              (term_of_ty ty)
                              (term_of_list term_of_ty tyl)
    | AtomTyUnpack v ->
         mk_atomTyUnpack_term (term_of_symbol v)

    | AtomUnop (op, a) ->
         mk_atomUnop_term     (term_of_unop op)
                              (term_of_atom a)
    | AtomBinop (op, a1, a2) ->
         mk_atomBinop_term    (term_of_binop op)
                              (term_of_atom a1)
                              (term_of_atom a2)


let rec atom_of_term t =
   if is_atomNil_term t then
      AtomNil  (ty_of_term (dest_atomNil_term t))

   else if is_atomInt_term t then
      AtomInt  (int_of_number_term (dest_atomInt_term t))
   else if is_atomEnum_term t then
      let bound, value = dest_atomEnum_term t in
         AtomEnum    (int_of_num bound)
                     (int_of_number_term value)
   else if is_atomRawInt_term t then
      let pre, sign, value =  dest_atomRawInt_term t in
         AtomRawInt  (rawint_of_number_term  (int_precision_of_num pre)
                                             (int_signed_of_string sign)
                                             value)
   else if is_atomFloat_term t then
      report_error "atom_of_term (float)" t

   else if is_atomVar_term t then
      AtomVar (symbol_of_term (dest_atomVar_term t))

   else if is_atomLabel_term t then
      let field, subfield, frame, r = dest_atomLabel_term t in
         AtomLabel   (((symbol_of_term frame),
                       (symbol_of_string field),
                       (symbol_of_string subfield)),
                      (rawint_of_number_term Int32 true r))
   else if is_atomSizeof_term t then
      let tvl, r = dest_atomSizeof_term t in
         AtomSizeof  ((list_of_term symbol_of_term tvl),
                      (rawint_of_number_term Int32 true r))
   else if is_atomConst_term t then
      let ty, tv, i = dest_atomConst_term t in
         AtomConst   ((ty_of_term ty),
                      (symbol_of_term tv),
                      (int_of_number_term i))

   else if is_atomTyApply_term t then
      let a, ty, tyl = dest_atomTyApply_term t in
         AtomTyApply ((atom_of_term a),
                      (ty_of_term ty),
                      (list_of_term ty_of_term tyl))
   else if is_atomTyPack_term t then
      let v, ty, tyl = dest_atomTyPack_term t in
         AtomTyPack  ((symbol_of_term v),
                      (ty_of_term ty),
                      (list_of_term ty_of_term tyl))
   else if is_atomTyUnpack_term t then
      AtomTyUnpack (symbol_of_term (dest_atomTyUnpack_term t))

   else if is_atomUnop_term t then
      let op, a = dest_atomUnop_term t in
         AtomUnop    ((unop_of_term op),
                      (atom_of_term a))
   else if is_atomBinop_term t then
      let op, a1, a2 = dest_atomBinop_term t in
         AtomBinop   ((binop_of_term op),
                      (atom_of_term a1),
                      (atom_of_term a2))

   else
      report_error "atom_of_term" t
