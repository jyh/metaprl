(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Operations for converting between MC Fir expressions and MetaPRL terms.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
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
 * Email:  emre@its.caltech.edu
 *)

(* Open MC ML namespaces. *)

open Rawint
open Rawfloat
open Fir

(* Open MetaPRL ML namespaces. *)

open Refiner.Refiner.RefineError
open Mp_mc_fir_exp
open Mp_mc_connect_base
open Mp_mc_connect_ty

(*
 * Convert to and from unop.
 *)

let term_of_unop op =
   match op with

      (* Identity (polymorphic). *)
      IdOp -> idOp_term

      (* Naml ints. *)
    | UMinusIntOp -> uminusIntOp_term
    | NotIntOp ->    notIntOp_term

      (* Bit fields. *)
    | RawBitFieldOp (p, s, i1, i2) ->
         mk_rawBitFieldOp_term  (term_of_int_precision p)
                                (term_of_int_signed s)
                                (number_term_of_int i1)
                                (number_term_of_int i2)

      (* Native ints. *)
    | UMinusRawIntOp (p, s) ->
         mk_uminusRawIntOp_term (term_of_int_precision p)
                                (term_of_int_signed s)
    | NotRawIntOp (p, s) ->
         mk_notRawIntOp_term    (term_of_int_precision p)
                                (term_of_int_signed s)

      (* Floats. *)
    | UMinusFloatOp p ->   mk_uminusFloatOp_term   (term_of_float_precision p)
    | AbsFloatOp p ->      mk_absFloatOp_term      (term_of_float_precision p)
    | SinOp p ->           mk_sinOp_term           (term_of_float_precision p)
    | CosOp p ->           mk_cosOp_term           (term_of_float_precision p)
    | SqrtOp p ->          mk_sqrtOp_term          (term_of_float_precision p)

      (* Coerce to int. *)
    | IntOfFloatOp p ->    mk_intOfFloatOp_term    (term_of_float_precision p)

      (* COerce to float. *)
    | FloatOfIntOp p ->
         mk_floatOfIntOp_term    (term_of_float_precision p)
    | FloatOfFloatOp (p1, p2) ->
         mk_floatOfFloatOp_term  (term_of_float_precision p1)
                                 (term_of_float_precision p2)
    | FloatOfRawIntOp (pf, pi, s) ->
         mk_floatOfRawIntOp_term (term_of_float_precision pf)
                                 (term_of_int_precision pi)
                                 (term_of_int_signed s)

      (* Coerce to rawint. *)
    | RawIntOfIntOp (p, s) ->
         mk_rawIntOfIntOp_term      (term_of_int_precision p)
                                    (term_of_int_signed s)
    | RawIntOfEnumOp (p, s, i) ->
         mk_rawIntOfEnumOp_term     (term_of_int_precision p)
                                    (term_of_int_signed s)
                                    (number_term_of_int i)
    | RawIntOfFloatOp (p, s, pf) ->
         mk_rawIntOfFloatOp_term    (term_of_int_precision p)
                                    (term_of_int_signed s)
                                    (term_of_float_precision pf)
    | RawIntOfRawIntOp (pd, sd, ps, ss) ->
         mk_rawIntOfRawIntOp_term   (term_of_int_precision pd)
                                    (term_of_int_signed sd)
                                    (term_of_int_precision ps)
                                    (term_of_int_signed ss)

      (* Integer/pointer coercions (only for C). *)
    | RawIntOfPointerOp (p, s) ->
         mk_rawIntOfPointerOp_term  (term_of_int_precision p)
                                    (term_of_int_signed s)
    | PointerOfRawIntOp (p, s) ->
         mk_pointerOfRawIntOp_term  (term_of_int_precision p)
                                    (term_of_int_signed s)

let unop_of_term t =

   (* Identity (polymorhpic). *)
   if is_idOp_term t then
      IdOp

   (* Naml ints. *)
   else if is_uminusIntOp_term t then
      UMinusIntOp
   else if is_notIntOp_term t then
      NotIntOp

   (* Bit fields. *)
   else if is_rawBitFieldOp_term t then
      let p, s, i1, i2 = dest_rawBitFieldOp_term t in
         RawBitFieldOp (int_precision_of_term p)
                       (int_signed_of_term s)
                       (int_of_number_term i1)
                       (int_of_number_term i2)

   (* Native ints. *)
   else if is_uminusRawIntOp_term t then
      let p, s = dest_uminusRawIntOp_term t in
         UMinusRawIntOp (int_precision_of_term p) (int_signed_of_term s)
   else if is_notRawIntOp_term t then
      let p, s = dest_notRawIntOp_term t in
         NotRawIntOp    (int_precision_of_term p) (int_signed_of_term s)

   (* Floats. *)
   else if is_uminusFloatOp_term t then
      UMinusFloatOp  (float_precision_of_term (dest_uminusFloatOp_term t))
   else if is_absFloatOp_term t then
      AbsFloatOp     (float_precision_of_term (dest_absFloatOp_term t))
   else if is_sinOp_term t then
      SinOp          (float_precision_of_term (dest_sinOp_term t))
   else if is_cosOp_term t then
      CosOp          (float_precision_of_term (dest_cosOp_term t))
   else if is_sqrtOp_term t then
      SqrtOp         (float_precision_of_term (dest_sqrtOp_term t))

   (* Coerce to int. *)
   else if is_intOfFloatOp_term t then
      IntOfFloatOp   (float_precision_of_term (dest_intOfFloatOp_term t))

   (* Coerce to float. *)
   else if is_floatOfIntOp_term t then
      FloatOfIntOp   (float_precision_of_term (dest_floatOfIntOp_term t))
   else if is_floatOfFloatOp_term t then
      let p1, p2 = dest_floatOfFloatOp_term t in
         FloatOfFloatOp    (float_precision_of_term p1)
                           (float_precision_of_term p2)
   else if is_floatOfRawIntOp_term t then
      let pf, pi, s = dest_floatOfRawIntOp_term t in
         FloatOfRawIntOp   (float_precision_of_term pf)
                           (int_precision_of_term pi)
                           (int_signed_of_term s)

   (* Coerce to rawint. *)
   else if is_rawIntOfIntOp_term t then
      let p, s = dest_rawIntOfIntOp_term t in
         RawIntOfIntOp     (int_precision_of_term p)
                           (int_signed_of_term s)
   else if is_rawIntOfEnumOp_term t then
      let p, s, i = dest_rawIntOfEnumOp_term t in
         RawIntOfEnumOp    (int_precision_of_term p)
                           (int_signed_of_term s)
                           (int_of_number_term i)
   else if is_rawIntOfFloatOp_term t then
      let pi, s, pf = dest_rawIntOfFloatOp_term t in
         RawIntOfFloatOp   (int_precision_of_term pi)
                           (int_signed_of_term s)
                           (float_precision_of_term pf)
   else if is_rawIntOfRawIntOp_term t then
      let pd, sd, ps, ss = dest_rawIntOfRawIntOp_term t in
         RawIntOfRawIntOp  (int_precision_of_term pd)
                           (int_signed_of_term sd)
                           (int_precision_of_term ps)
                           (int_signed_of_term ss)

   (* Integer/pointer coercions (only for C). *)
   else if is_rawIntOfPointerOp_term t then
      let p, s = dest_rawIntOfPointerOp_term t in
         RawIntOfPointerOp (int_precision_of_term p)
                           (int_signed_of_term s)
   else if is_pointerOfRawIntOp_term t then
      let p, s = dest_pointerOfRawIntOp_term t in
         PointerOfRawIntOp (int_precision_of_term p)
                           (int_signed_of_term s)

   else
      raise (RefineError ("unop_of_term", StringTermError
            ("not a unop", t)))

(*
 * Convert to and from binop.
 *)

let term_of_binop op =
   match op with

      (* Enums. *)
      AndEnumOp i -> mk_andEnumOp_term (number_term_of_int i)
    | OrEnumOp i ->  mk_orEnumOp_term  (number_term_of_int i)
    | XorEnumOp i -> mk_xorEnumOp_term (number_term_of_int i)

      (* Naml ints. *)
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

      (* Native ints. *)
    | PlusRawIntOp (p, s) ->
         mk_plusRawIntOp_term (term_of_int_precision p) (term_of_int_signed s)
    | MinusRawIntOp (p, s) ->
         mk_minusRawIntOp_term (term_of_int_precision p) (term_of_int_signed s)
    | MulRawIntOp (p, s) ->
         mk_mulRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | DivRawIntOp (p, s) ->
         mk_divRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | RemRawIntOp (p, s) ->
         mk_remRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | SlRawIntOp (p, s) ->
         mk_slRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | SrRawIntOp (p, s) ->
         mk_srRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | AndRawIntOp (p, s) ->
         mk_andRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | OrRawIntOp (p, s) ->
         mk_orRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | XorRawIntOp (p, s) ->
         mk_xorRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | MaxRawIntOp (p, s) ->
         mk_maxRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | MinRawIntOp (p, s) ->
         mk_minRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)

    | RawSetBitFieldOp (p, s, i1, i2) ->
         mk_rawSetBitFieldOp_term (term_of_int_precision p)
                                  (term_of_int_signed s)
                                  (number_term_of_int i1)
                                  (number_term_of_int i2)

    | EqRawIntOp (p, s) ->
         mk_eqRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | NeqRawIntOp (p, s) ->
         mk_neqRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | LtRawIntOp (p, s) ->
         mk_ltRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | LeRawIntOp (p, s) ->
         mk_leRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | GtRawIntOp (p, s) ->
         mk_gtRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | GeRawIntOp (p,  s) ->
         mk_geRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | CmpRawIntOp (p, s) ->
         mk_cmpRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)

      (* Floats. *)
    | PlusFloatOp p ->  mk_plusFloatOp_term  (term_of_float_precision p)
    | MinusFloatOp p -> mk_minusFloatOp_term (term_of_float_precision p)
    | MulFloatOp p ->   mk_mulFloatOp_term   (term_of_float_precision p)
    | DivFloatOp p ->   mk_divFloatOp_term   (term_of_float_precision p)
    | RemFloatOp p ->   mk_remFloatOp_term   (term_of_float_precision p)
    | MaxFloatOp p ->   mk_maxFloatOp_term   (term_of_float_precision p)
    | MinFloatOp p ->   mk_minFloatOp_term   (term_of_float_precision p)

    | EqFloatOp p ->    mk_eqFloatOp_term    (term_of_float_precision p)
    | NeqFloatOp p ->   mk_neqFloatOp_term   (term_of_float_precision p)
    | LtFloatOp p ->    mk_ltFloatOp_term    (term_of_float_precision p)
    | LeFloatOp p ->    mk_leFloatOp_term    (term_of_float_precision p)
    | GtFloatOp p ->    mk_gtFloatOp_term    (term_of_float_precision p)
    | GeFloatOp p ->    mk_geFloatOp_term    (term_of_float_precision p)
    | CmpFloatOp p ->   mk_cmpFloatOp_term   (term_of_float_precision p)

    | Atan2Op p ->      mk_atan2Op_term      (term_of_float_precision p)

      (* Pointer equality. *)
    | EqEqOp ->   eqEqOp_term
    | NeqEqOp ->  neqEqOp_term

      (* Pointer arithmetic. *)
    | PlusPointerOp (p, s) ->
         mk_plusPointerOp_term   (term_of_int_precision p)
                                 (term_of_int_signed s)

let binop_of_term t =

   (* Enums. *)
   if is_andEnumOp_term t then
      AndEnumOp   (int_of_number_term (dest_andEnumOp_term t))
   else if is_orEnumOp_term t then
      OrEnumOp    (int_of_number_term (dest_orEnumOp_term t))
   else if is_xorEnumOp_term t then
      XorEnumOp   (int_of_number_term (dest_xorEnumOp_term t))

   (* Naml ints. *)
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

   (* Native ints. *)
   else if is_plusRawIntOp_term t then
      let p, s = dest_plusRawIntOp_term t in
         PlusRawIntOp   (int_precision_of_term p) (int_signed_of_term s)
   else if is_minusRawIntOp_term t then
      let p, s = dest_minusRawIntOp_term t in
         MinusRawIntOp  (int_precision_of_term p) (int_signed_of_term s)
   else if is_mulRawIntOp_term t then
      let p, s = dest_mulRawIntOp_term t in
         MulRawIntOp    (int_precision_of_term p) (int_signed_of_term s)
   else if is_divRawIntOp_term t then
      let p, s = dest_divRawIntOp_term t in
         DivRawIntOp    (int_precision_of_term p) (int_signed_of_term s)
   else if is_remRawIntOp_term t then
      let p, s = dest_remRawIntOp_term t in
         RemRawIntOp    (int_precision_of_term p) (int_signed_of_term s)
   else if is_slRawIntOp_term t then
      let p, s = dest_slRawIntOp_term t in
         SlRawIntOp     (int_precision_of_term p) (int_signed_of_term s)
   else if is_srRawIntOp_term t then
      let p, s = dest_srRawIntOp_term t in
         SrRawIntOp     (int_precision_of_term p) (int_signed_of_term s)
   else if is_andRawIntOp_term t then
      let p, s = dest_andRawIntOp_term t in
         AndRawIntOp    (int_precision_of_term p) (int_signed_of_term s)
   else if is_orRawIntOp_term t then
      let p, s = dest_orRawIntOp_term t in
         OrRawIntOp     (int_precision_of_term p) (int_signed_of_term s)
   else if is_xorRawIntOp_term t then
      let p, s = dest_xorRawIntOp_term t in
         XorRawIntOp    (int_precision_of_term p) (int_signed_of_term s)
   else if is_maxRawIntOp_term t then
      let p, s = dest_maxRawIntOp_term t in
         MaxRawIntOp    (int_precision_of_term p) (int_signed_of_term s)
   else if is_minRawIntOp_term t then
      let p, s = dest_minRawIntOp_term t in
         MinRawIntOp    (int_precision_of_term p) (int_signed_of_term s)

   else if is_rawSetBitFieldOp_term t then
      let p, s, i1, i2 = dest_rawSetBitFieldOp_term t in
         RawSetBitFieldOp (int_precision_of_term p)
                          (int_signed_of_term s)
                          (int_of_number_term i1)
                          (int_of_number_term i2)

   else if is_eqRawIntOp_term t then
      let p, s = dest_eqRawIntOp_term t in
         EqRawIntOp     (int_precision_of_term p) (int_signed_of_term s)
   else if is_neqRawIntOp_term t then
      let p, s = dest_neqRawIntOp_term t in
         NeqRawIntOp    (int_precision_of_term p) (int_signed_of_term s)
   else if is_ltRawIntOp_term t then
      let p, s = dest_ltRawIntOp_term t in
         LtRawIntOp     (int_precision_of_term p) (int_signed_of_term s)
   else if is_leRawIntOp_term t then
      let p, s = dest_leRawIntOp_term t in
         LeRawIntOp     (int_precision_of_term p) (int_signed_of_term s)
   else if is_gtRawIntOp_term t then
      let p, s = dest_gtRawIntOp_term t in
         GtRawIntOp     (int_precision_of_term p) (int_signed_of_term s)
   else if is_geRawIntOp_term t then
      let p, s = dest_geRawIntOp_term t in
         GeRawIntOp     (int_precision_of_term p) (int_signed_of_term s)
   else if is_cmpRawIntOp_term t then
      let p, s = dest_cmpRawIntOp_term t in
         CmpRawIntOp    (int_precision_of_term p) (int_signed_of_term s)

   (* Floats. *)
   else if is_plusFloatOp_term t then
      PlusFloatOp    (float_precision_of_term (dest_plusFloatOp_term t))
   else if is_minusFloatOp_term t then
      MinusFloatOp   (float_precision_of_term (dest_minusFloatOp_term t))
   else if is_mulFloatOp_term t then
      MulFloatOp     (float_precision_of_term (dest_mulFloatOp_term t))
   else if is_divFloatOp_term t then
      DivFloatOp     (float_precision_of_term (dest_divFloatOp_term t))
   else if is_remFloatOp_term t then
      RemFloatOp     (float_precision_of_term (dest_remFloatOp_term t))
   else if is_maxFloatOp_term t then
      MaxFloatOp     (float_precision_of_term (dest_maxFloatOp_term t))
   else if is_minFloatOp_term t then
      MinFloatOp     (float_precision_of_term (dest_minFloatOp_term t))

   else if is_eqFloatOp_term t then
      EqFloatOp      (float_precision_of_term (dest_eqFloatOp_term t))
   else if is_neqFloatOp_term t then
      NeqFloatOp     (float_precision_of_term (dest_neqFloatOp_term t))
   else if is_ltFloatOp_term t then
      LtFloatOp      (float_precision_of_term (dest_ltFloatOp_term t))
   else if is_leFloatOp_term t then
      LeFloatOp      (float_precision_of_term (dest_leFloatOp_term t))
   else if is_gtFloatOp_term t then
      GtFloatOp      (float_precision_of_term (dest_gtFloatOp_term t))
   else if is_geFloatOp_term t then
      GeFloatOp      (float_precision_of_term (dest_geFloatOp_term t))
   else if is_cmpFloatOp_term t then
      CmpFloatOp     (float_precision_of_term (dest_cmpFloatOp_term t))

   else if is_atan2Op_term t then
      Atan2Op        (float_precision_of_term (dest_atan2Op_term t))

   (* Pointer equality. *)
   else if is_eqEqOp_term t then
      EqEqOp
   else if is_neqEqOp_term t then
      NeqEqOp

   (* Pointer arithmetic. *)
   else if is_plusPointerOp_term t then
      let p, s = dest_plusPointerOp_term t in
         PlusPointerOp  (int_precision_of_term p)
                        (int_signed_of_term s)

   else
      raise (RefineError ("binop_of_term", StringTermError
            ("not a binop", t)))

(*
 * Convert to and from subscripting terms.
 *)

let term_of_sub_block b =
   match b with
      BlockSub ->    blockSub_term
    | RawDataSub ->  rawDataSub_term
    | TupleSub ->    tupleSub_term
    | RawTupleSub -> rawTupleSub_term

let sub_block_of_term t =
   if is_blockSub_term t then
      BlockSub
   else if is_rawDataSub_term t then
      RawDataSub
   else if is_tupleSub_term t then
      TupleSub
   else if is_rawTupleSub_term t then
      RawTupleSub

   else
      raise (RefineError ("sub_block_of_term", StringTermError
            ("not a sub_block", t)))

let term_of_sub_value v =
   match v with
      PolySub ->           polySub_term
    | RawIntSub (p, s) ->  mk_rawIntSub_term (term_of_int_precision p)
                                             (term_of_int_signed s)
    | RawFloatSub p ->     mk_rawFloatSub_term (term_of_float_precision p)
    | PointerSub ->        pointerSub_term
    | FunctionSub ->       functionSub_term

let sub_value_of_term t =
   if is_polySub_term t then
      PolySub
   else if is_rawIntSub_term t then
      let p, s = dest_rawIntSub_term t in
         RawIntSub   (int_precision_of_term p)
                     (int_signed_of_term s)
   else if is_rawFloatSub_term t then
      RawFloatSub (float_precision_of_term (dest_rawFloatSub_term t))
   else if is_pointerSub_term t then
      PointerSub
   else if is_functionSub_term t then
      FunctionSub

   else
      raise (RefineError ("sub_value_of_term", StringTermError
            ("not a sub_value", t)))

let term_of_sub_index i =
   match i with
      ByteIndex -> byteIndex_term
    | WordIndex -> wordIndex_term

let sub_index_of_term t =
   if is_byteIndex_term t then
      ByteIndex
   else if is_wordIndex_term t then
      WordIndex

   else
      raise (RefineError ("sub_index_of_term", StringTermError
            ("not a sub_index", t)))

let term_of_sub_script t =
   match t with
      IntIndex ->             intIndex_term
    | RawIntIndex (p, s) ->   mk_rawIntIndex_term (term_of_int_precision p)
                                                  (term_of_int_signed s)

let sub_script_of_term t =
   if is_intIndex_term t then
      IntIndex
   else if is_rawIntIndex_term t then
      let p, s = dest_rawIntIndex_term t in
         RawIntIndex (int_precision_of_term p)
                     (int_signed_of_term s)

   else
      raise (RefineError ("sub_script_of_term", StringTermError
            ("not a sub_script", t)))

let term_of_subop op =
   mk_subop_term        (term_of_sub_block op.sub_block)
                        (term_of_sub_value op.sub_value)
                        (term_of_sub_index op.sub_index)
                        (term_of_sub_script op.sub_script)

let subop_of_term t =
   if is_subop_term t then
      let block, value, index, script = dest_subop_term t in
         {  sub_block = sub_block_of_term block;
            sub_value = sub_value_of_term value;
            sub_index = sub_index_of_term index;
            sub_script = sub_script_of_term script
         }

   else
      raise (RefineError ("subop_of_term", StringTermError
            ("not a subop", t)))

(*
 * Convert to and from atom.
 *)

let term_of_atom a =
   match a with
      AtomNil t ->
         mk_atomNil_term      (term_of_ty t)
    | AtomInt i ->
         mk_atomInt_term      (number_term_of_int i)
    | AtomEnum (i1, i2) ->
         mk_atomEnum_term     (number_term_of_int i1) (number_term_of_int i2)
    | AtomRawInt r ->
         mk_atomRawInt_term   (term_of_int_precision (Rawint.precision r))
                              (term_of_int_signed (signed r))
                              (number_term_of_rawint r)
    | AtomFloat f ->
         mk_atomFloat_term    (term_of_float_precision (Rawfloat.precision f))
                              (number_term_of_rawfloat f)
    | AtomConst (t, tv, i) ->
         mk_atomConst_term    (term_of_ty t)
                              (term_of_ty_var tv)
                              (number_term_of_int i)
    | AtomVar v ->
         mk_atomVar_term      (term_of_var v)

let atom_of_term t =
   if is_atomNil_term t then
      AtomNil (ty_of_term (dest_atomNil_term t))
   else if is_atomInt_term t then
      AtomInt (int_of_number_term (dest_atomInt_term t))
   else if is_atomEnum_term t then
      let i1, i2 = dest_atomEnum_term t in
         AtomEnum (int_of_number_term i1) (int_of_number_term i2)
   else if is_atomRawInt_term t then
      let p, s, i = dest_atomRawInt_term t in
         AtomRawInt (rawint_of_number_term (int_precision_of_term p)
                                           (int_signed_of_term s)
                                           i)
   else if is_atomFloat_term t then
      let p, f = dest_atomFloat_term t in
         AtomFloat (rawfloat_of_number_term (float_precision_of_term p) f)
   else if is_atomConst_term t then
      let t, tv, i = dest_atomConst_term t in
         AtomConst (ty_of_term t) (ty_var_of_term tv) (int_of_number_term i)
   else if is_atomVar_term t then
      AtomVar (var_of_term (dest_atomVar_term t))

   else
      raise (RefineError ("atom_of_term", StringTermError
            ("not an atom", t)))

(*
 * Convert to and from alloc_op.
 *)

let term_of_alloc_op op =
   match op with
      AllocTuple (tc, t, al) ->
         mk_allocTuple_term   (term_of_tuple_class tc)
                              (term_of_ty t)
                              (term_of_list term_of_atom al)
    | AllocUnion (t, tv, i, al) ->
         mk_allocUnion_term   (term_of_ty t)
                              (term_of_ty_var tv)
                              (number_term_of_int i)
                              (term_of_list term_of_atom al)
    | AllocArray (t, al) ->
         mk_allocArray_term   (term_of_ty t)
                              (term_of_list term_of_atom al)
    | AllocVArray (t, si, a1, a2) ->
         mk_allocVArray_term  (term_of_ty t)
                              (term_of_sub_index si)
                              (term_of_atom a1)
                              (term_of_atom a2)
    | AllocMalloc (t, a) ->
         mk_allocMalloc_term  (term_of_ty t)
                              (term_of_atom a)

let alloc_op_of_term t =
   if is_allocTuple_term t then
      let tc, t, al = dest_allocTuple_term t in
         AllocTuple  (tuple_class_of_term tc)
                     (ty_of_term t)
                     (list_of_term atom_of_term al)
   else if is_allocUnion_term t then
      let t, tv, i, al = dest_allocUnion_term t in
         AllocUnion  (ty_of_term t)
                     (ty_var_of_term tv)
                     (int_of_number_term i)
                     (list_of_term atom_of_term al)
   else if is_allocArray_term t then
      let t, al = dest_allocArray_term t in
         AllocArray  (ty_of_term t)
                     (list_of_term atom_of_term al)
   else if is_allocVArray_term t then
      let t, si, a1, a2 = dest_allocVArray_term t in
         AllocVArray (ty_of_term t)
                     (sub_index_of_term si)
                     (atom_of_term a1)
                     (atom_of_term a2)
   else if is_allocMalloc_term t then
      let t, a = dest_allocMalloc_term t in
         AllocMalloc (ty_of_term t)
                     (atom_of_term a)

   else
      raise (RefineError ("term_of_alloc_op", StringTermError
            ("not an alloc_op", t)))

(*
 * Convert to and from tailop.
 *)

let term_of_tailop t =
   match t with
      TailSysMigrate (i, a1, a2, v, al) ->
         mk_tailSysMigrate_term     (number_term_of_int i)
                                    (term_of_atom a1)
                                    (term_of_atom a2)
                                    (term_of_var v)
                                    (term_of_list term_of_atom al)
    | TailAtomic (v, a, al) ->
         mk_tailAtomic_term         (term_of_var v)
                                    (term_of_atom a)
                                    (term_of_list term_of_atom al)
    | TailAtomicRollback a ->
         mk_tailAtomicRollback_term (term_of_atom a)
    | TailAtomicCommit (v, al) ->
         mk_tailAtomicCommit_term   (term_of_var v)
                                    (term_of_list term_of_atom al)

let tailop_of_term t =
   if is_tailSysMigrate_term t then
      let i, a1, a2, v, al = dest_tailSysMigrate_term t in
         TailSysMigrate       (int_of_number_term i)
                              (atom_of_term a1)
                              (atom_of_term a2)
                              (var_of_term v)
                              (list_of_term atom_of_term al)
   else if is_tailAtomic_term t then
      let v, a, al = dest_tailAtomic_term t in
         TailAtomic           (var_of_term v)
                              (atom_of_term a)
                              (list_of_term atom_of_term al)
   else if is_tailAtomicRollback_term t then
      TailAtomicRollback (atom_of_term (dest_tailAtomicRollback_term t))
   else if is_tailAtomicCommit_term t then
      let v, al = dest_tailAtomicCommit_term t in
         TailAtomicCommit     (var_of_term v)
                              (list_of_term atom_of_term al)

   else
      raise (RefineError ("term_of_tailop", StringTermError
            ("not a tailop", t)))

(*
 * Convert to and from predicate / assertion terms.
 *)

let term_of_pred_nop op =
   match op with
      IsMutable -> isMutable_term

let pred_nop_of_term t =
   if is_isMutable_term t then
      IsMutable

   else
      raise (RefineError ("pred_nop_of_term", StringTermError
            ("not a pred_nop", t)))

let term_of_pred_unop op =
   match op with
      Reserve ->           reserve_term
    | BoundsCheckLower ->  boundsCheckLower_term
    | BoundsCheckUpper ->  boundsCheckUpper_term
    | PolyCheck ->         polyCheck_term
    | PointerCheck ->      pointerCheck_term
    | FunctionCheck ->     functionCheck_term

let pred_unop_of_term t =
   if is_reserve_term t then
      Reserve
   else if is_boundsCheckLower_term t then
      BoundsCheckLower
   else if is_boundsCheckUpper_term t then
      BoundsCheckUpper
   else if is_polyCheck_term t then
      PolyCheck
   else if is_pointerCheck_term t then
      PointerCheck
   else if is_functionCheck_term t then
      FunctionCheck

   else
      raise (RefineError ("pred_unop_of_term", StringTermError
            ("not a pred_unop", t)))

let term_of_pred_binop op =
   match op with
      BoundsCheck -> boundsCheck_term

let pred_binop_of_term t =
   if is_boundsCheck_term t then
      BoundsCheck

   else
      raise (RefineError ("pred_binop_of_term", StringTermError
            ("not a pred_binop", t)))

let term_of_pred p =
   match p with
      PredNop (v, op) ->
         mk_predNop_term         (term_of_var v)
                                 (term_of_pred_nop op)
    | PredUnop (v, op, a) ->
         mk_predUnop_term        (term_of_var v)
                                 (term_of_pred_unop op)
                                 (term_of_atom a)
    | PredBinop (v, op, a1, a2) ->
         mk_predBinop_term       (term_of_var v)
                                 (term_of_pred_binop op)
                                 (term_of_atom a1)
                                 (term_of_atom a2)

let pred_of_term t =
   if is_predNop_term t then
      let v, op = dest_predNop_term t in
         PredNop           (var_of_term v)
                           (pred_nop_of_term op)
   else if is_predUnop_term t then
      let v, op, a = dest_predUnop_term t in
         PredUnop          (var_of_term v)
                           (pred_unop_of_term op)
                           (atom_of_term a)
   else if is_predBinop_term t then
      let v, op, a1, a2 = dest_predBinop_term t in
         PredBinop         (var_of_term v)
                           (pred_binop_of_term op)
                           (atom_of_term a1)
                           (atom_of_term a2)

   else
      raise (RefineError ("pred_of_term", StringTermError
            ("not a pred", t)))

(*
 * Convert debugging info to and from terms.
 *)

(* Helper functions. *)

let term_of_debug_var (v1, t, v2) =
   mk_debugVarItem_term (term_of_var v1) (term_of_ty t) (term_of_var v2)

let debug_var_of_term t =
   if is_debugVarItem_term t then
      let v1, t, v2 = dest_debugVarItem_term t in
         (var_of_term v1), (ty_of_term t), (var_of_term v2)
   else
      raise (RefineError ("debug_var_of_term", StringTermError
            ("not a debug_var", t)))

(* Actual functions. *)

let term_of_debug_line (str, i) =
   mk_debugLine_term (term_of_string str) (number_term_of_int i)

let debug_line_of_term t =
   if is_debugLine_term t then
      let str, i = dest_debugLine_term t in
         (string_of_term str), (int_of_number_term i)
   else
      raise (RefineError ("debug_line_of_term", StringTermError
            ("not a debug_line", t)))

let term_of_debug_vars vars =
   term_of_list term_of_debug_var vars

let debug_vars_of_term t =
   list_of_term debug_var_of_term t

let term_of_debug_info info =
   match info with
      DebugString str ->
         mk_debugString_term  (term_of_string str)
    | DebugContext (line, vars) ->
         mk_debugContext_term (term_of_debug_line line)
                              (term_of_debug_vars vars)

let debug_info_of_term t =
   if is_debugString_term t then
      DebugString (string_of_term (dest_debugString_term t))
   else if is_debugContext_term t then
      let line, vars = dest_debugContext_term t in
         DebugContext (debug_line_of_term line)
                      (debug_vars_of_term vars)
   else
      raise (RefineError ("debug_info_of_term", StringTermError
            ("not a debug_info", t)))

(*
 * Convert to and from exp.
 *)

(* Helper functions. *)

let rec term_of_case (set, expr) =
   mk_matchCase_term (term_of_set set) (term_of_exp expr)

and case_of_term t =
   if is_matchCase_term t then
      let set, expr = dest_matchCase_term t in
         (set_of_term set), (exp_of_term expr)
   else
      raise (RefineError ("case of term", StringTermError
            ("not a match case (set * exp)", t)))

(* Actual functions. *)

and term_of_exp e =
   match e with

      (* Primitive operations. *)
      LetUnop (v, ty, op, a, expr) ->
         mk_letUnop_term         (term_of_ty ty)
                                 (term_of_unop op)
                                 (term_of_atom a)
                                 (string_of_var v)
                                 (term_of_exp expr)
    | LetBinop (v, ty, op, a1, a2, expr) ->
         mk_letBinop_term        (term_of_ty ty)
                                 (term_of_binop op)
                                 (term_of_atom a1)
                                 (term_of_atom a2)
                                 (string_of_var v)
                                 (term_of_exp expr)

      (* Function application. *)
    | LetExt (v, ty1, str, ty2, al, expr) ->
         mk_letExt_term          (term_of_ty ty1)
                                 (term_of_string str)
                                 (term_of_ty ty2)
                                 (term_of_list term_of_atom al)
                                 (string_of_var v)
                                 (term_of_exp expr)
    | TailCall (v, al) ->
         mk_tailCall_term        (term_of_var v)
                                 (term_of_list term_of_atom al)
    | SpecialCall op ->
         mk_specialCall_term     (term_of_tailop op)

      (* Control. *)
    | Match (a, cases) ->
         mk_matchExp_term        (term_of_atom a)
                                 (term_of_list term_of_case cases)
    | TypeCase (a1, a2, v1, v2, expr1, expr2) ->
         mk_typeCase_term        (term_of_atom a1)
                                 (term_of_atom a2)
                                 (term_of_var v1)
                                 (term_of_var v2)
                                 (term_of_exp expr1)
                                 (term_of_exp expr2)

      (* Allocation. *)
    | LetAlloc (v, op, expr) ->
         mk_letAlloc_term        (string_of_var v)
                                 (term_of_alloc_op op)
                                 (term_of_exp expr)

      (* Subscripting. *)
    | LetSubscript (sop, v1, t, v2, a, expr) ->
         mk_letSubscript_term    (term_of_subop sop)
                                 (term_of_ty t)
                                 (term_of_var v2)
                                 (term_of_atom a)
                                 (string_of_var v1)
                                 (term_of_exp expr)
    | SetSubscript (sop, lbl, v, a1, t, a2, expr) ->
         mk_setSubscript_term    (term_of_subop sop)
                                 (term_of_label lbl)
                                 (term_of_var v)
                                 (term_of_atom a1)
                                 (term_of_ty t)
                                 (term_of_atom a2)
                                 (term_of_exp expr)
    | SetGlobal (svl, lbl, v, t, a, expr) ->
         mk_setGlobal_term       (term_of_sub_value svl)
                                 (term_of_label lbl)
                                 (term_of_var v)
                                 (term_of_ty t)
                                 (term_of_atom a)
                                 (term_of_exp expr)
    | Memcpy (sop, lbl, v1, a1, v2, a2, a3, expr) ->
         mk_memcpy_term          (term_of_subop sop)
                                 (term_of_label lbl)
                                 (term_of_var v1)
                                 (term_of_atom a1)
                                 (term_of_var v2)
                                 (term_of_atom a2)
                                 (term_of_atom a3)
                                 (term_of_exp expr)

      (* Assertions. *)
    | Call (v, aol, expr) ->
         mk_call_term         (term_of_var v)
                              (term_of_list (term_of_option term_of_atom) aol)
                              (term_of_exp expr)
    | Assert (lbl, p, expr) ->
         mk_assertExp_term       (term_of_label lbl)
                                 (term_of_pred p)
                                 (term_of_exp expr)

      (* Debugging. *)
    | Debug (info, expr) ->
         mk_debug_term           (term_of_debug_info info)
                                 (term_of_exp expr)

and exp_of_term t =

   (* Primitive operations. *)
   if is_letUnop_term t then
      let ty, op, a, v, expr = dest_letUnop_term t in
         LetUnop           (var_of_string v)
                           (ty_of_term ty)
                           (unop_of_term op)
                           (atom_of_term a)
                           (exp_of_term expr)
   else if is_letBinop_term t then
      let ty, op, a1, a2, v, expr = dest_letBinop_term t in
         LetBinop          (var_of_string v)
                           (ty_of_term ty)
                           (binop_of_term op)
                           (atom_of_term a1)
                           (atom_of_term a2)
                           (exp_of_term expr)

   (* Function application. *)
   else if is_letExt_term t then
      let ty1, str, ty2, al, v, expr = dest_letExt_term t in
         LetExt            (var_of_string v)
                           (ty_of_term ty1)
                           (string_of_term str)
                           (ty_of_term ty2)
                           (list_of_term atom_of_term al)
                           (exp_of_term expr)
   else if is_tailCall_term t then
      let v, al = dest_tailCall_term t in
         TailCall          (var_of_term v)
                           (list_of_term atom_of_term al)
   else if is_specialCall_term t then
         SpecialCall       (tailop_of_term (dest_specialCall_term t))

   (* Control. *)
   else if is_matchExp_term t then
      let a, cases = dest_matchExp_term t in
         Match             (atom_of_term a)
                           (list_of_term case_of_term cases)
   else if is_typeCase_term t then
      let  a1, a2, v1, v2, expr1, expr2 = dest_typeCase_term t in
         TypeCase          (atom_of_term a1)
                           (atom_of_term a2)
                           (var_of_term v1)
                           (var_of_term v2)
                           (exp_of_term expr1)
                           (exp_of_term expr2)

   (* Allocation. *)
   else if is_letAlloc_term t then
      let v, op, expr = dest_letAlloc_term t in
         LetAlloc          (var_of_string v)
                           (alloc_op_of_term op)
                           (exp_of_term expr)

   (* Subscripting. *)
   else if is_letSubscript_term t then
      let sop, t, v2, a, v1, expr = dest_letSubscript_term t in
         LetSubscript      (subop_of_term sop)
                           (var_of_string v1)
                           (ty_of_term t)
                           (var_of_term v2)
                           (atom_of_term a)
                           (exp_of_term expr)
   else if is_setSubscript_term t then
      let sop, lbl, v, a1, t, a2, expr = dest_setSubscript_term t in
         SetSubscript      (subop_of_term sop)
                           (label_of_term lbl)
                           (var_of_term v)
                           (atom_of_term a1)
                           (ty_of_term t)
                           (atom_of_term a2)
                           (exp_of_term expr)
   else if is_setGlobal_term t then
      let svl, lbl, v, t, a, expr = dest_setGlobal_term t in
         SetGlobal         (sub_value_of_term svl)
                           (label_of_term lbl)
                           (var_of_term v)
                           (ty_of_term t)
                           (atom_of_term a)
                           (exp_of_term expr)
   else if is_memcpy_term t then
      let sop, lbl, v1, a1, v2, a2, a3, expr = dest_memcpy_term t in
         Memcpy            (subop_of_term sop)
                           (label_of_term lbl)
                           (var_of_term v1)
                           (atom_of_term a1)
                           (var_of_term v2)
                           (atom_of_term a2)
                           (atom_of_term a3)
                           (exp_of_term expr)

   (* Assertions. *)
   else if is_call_term t then
      let v, aol, expr = dest_call_term t in
         Call              (var_of_term v)
                           (list_of_term (option_of_term atom_of_term) aol)
                           (exp_of_term expr)
   else if is_assertExp_term t then
      let lbl, p, expr = dest_assertExp_term t in
         Assert            (label_of_term lbl)
                           (pred_of_term p)
                           (exp_of_term expr)

   (* Debugging. *)
   else if is_debug_term t then
      let info, expr = dest_debug_term t in
         Debug             (debug_info_of_term info)
                           (exp_of_term expr)

   else
      raise (RefineError ("exp_of_term", StringTermError
            ("not an exp",  t)))

(*
 * Convert to and from fundef.
 *)

let term_of_fundef (line, ty, vars, exp) =
   mk_fundef_term    (term_of_debug_line line)
                     (term_of_ty ty)
                     (term_of_list term_of_var vars)
                     (term_of_exp exp)

let fundef_of_term t =
   if is_fundef_term t then
      let line, ty, vars, exp = dest_fundef_term t in
         (debug_line_of_term line),
         (ty_of_term ty),
         (list_of_term var_of_term vars),
         (exp_of_term exp)

   else
      raise (RefineError ("fundef_of_term", StringTermError
            ("not a fundef", t)))
