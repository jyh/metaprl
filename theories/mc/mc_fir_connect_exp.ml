(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Operations for converting between MC Fir expressions and MetaPRL terms.
 *
 * ----------------------------------------------------------------
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

open Fir

(* Open MetaPRL ML namespaces. *)

open Fir_exp
open Mc_fir_connect_base
open Mc_fir_connect_ty

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

let unop_of_term t =

   (* Identity (polymorhpic). *)
   if is_idOp_term t then
      IdOp

   (* Naml ints. *)
   else if is_uminusIntOp_term t then
      UMinusIntOp
   else if is_notIntOp_term t then
      NotIntOp

   else
      raise (Invalid_argument "unop_of_term: not a unop")

(*
 * Convert to and from binop.
 *)

let term_of_binop op =
   match op with

      (* Enumerations. *)
      AndEnumOp i -> mk_andEnumOp_term (number_term_of_int i)
    | OrEnumOp i ->  mk_orEnumOp_term (number_term_of_int i)

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
    | PlusRawIntOp (p,s) ->
         mk_plusRawIntOp_term (term_of_int_precision p) (term_of_int_signed s)
    | MinusRawIntOp (p,s) ->
         mk_minusRawIntOp_term (term_of_int_precision p) (term_of_int_signed s)
    | MulRawIntOp (p,s) ->
         mk_mulRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | DivRawIntOp (p,s) ->
         mk_divRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | RemRawIntOp (p,s) ->
         mk_remRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | SlRawIntOp (p,s) ->
         mk_slRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | SrRawIntOp (p,s) ->
         mk_srRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | AndRawIntOp (p,s) ->
         mk_andRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | OrRawIntOp (p,s) ->
         mk_orRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | XorRawIntOp (p,s) ->
         mk_xorRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | MaxRawIntOp (p,s) ->
         mk_maxRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | MinRawIntOp (p,s) ->
         mk_minRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)

    | RawSetBitFieldOp (p, s, i1, i2) ->
         mk_rawSetBitFieldOp_term (term_of_int_precision p)
                                  (term_of_int_signed s)
                                  (number_term_of_int i1)
                                  (number_term_of_int i2)

    | EqRawIntOp (p,s) ->
         mk_eqRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | NeqRawIntOp (p,s) ->
         mk_neqRawIntOp_term  (term_of_int_precision p) (term_of_int_signed s)
    | LtRawIntOp (p,s) ->
         mk_ltRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | LeRawIntOp (p,s) ->
         mk_leRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | GtRawIntOp (p,s) ->
         mk_gtRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | GeRawIntOp (p,s) ->
         mk_geRawIntOp_term   (term_of_int_precision p) (term_of_int_signed s)
    | CmpRawIntOp (p,s) ->
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

let binop_of_term t =

   (* Enumerations. *)
   if is_andEnumOp_term t then
      AndEnumOp (int_of_number_term (dest_andEnumOp_term t))
   else if is_orEnumOp_term t then
      OrEnumOp (int_of_number_term (dest_orEnumOp_term t))

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
      let p = dest_plusFloatOp_term t in
         PlusFloatOp    (float_precision_of_term p)
   else if is_minusFloatOp_term t then
      let p = dest_minusFloatOp_term t in
         MinusFloatOp   (float_precision_of_term p)
   else if is_mulFloatOp_term t then
      let p = dest_mulFloatOp_term t in
         MulFloatOp     (float_precision_of_term p)
   else if is_divFloatOp_term t then
      let p = dest_divFloatOp_term t in
         DivFloatOp     (float_precision_of_term p)
   else if is_remFloatOp_term t then
      let p = dest_remFloatOp_term t in
         RemFloatOp     (float_precision_of_term p)
   else if is_maxFloatOp_term t then
      let p = dest_maxFloatOp_term t in
         MaxFloatOp     (float_precision_of_term p)
   else if is_minFloatOp_term t then
      let p = dest_minFloatOp_term t in
         MinFloatOp     (float_precision_of_term p)

   else if is_eqFloatOp_term t then
      let p = dest_eqFloatOp_term t in
         EqFloatOp      (float_precision_of_term p)
   else if is_neqFloatOp_term t then
      let p = dest_neqFloatOp_term t in
         NeqFloatOp     (float_precision_of_term p)
   else if is_ltFloatOp_term t then
      let p = dest_ltFloatOp_term t in
         LtFloatOp      (float_precision_of_term p)
   else if is_leFloatOp_term t then
      let p = dest_leFloatOp_term t in
         LeFloatOp      (float_precision_of_term p)
   else if is_gtFloatOp_term t then
      let p = dest_gtFloatOp_term t in
         GtFloatOp      (float_precision_of_term p)
   else if is_geFloatOp_term t then
      let p = dest_geFloatOp_term t in
         GeFloatOp      (float_precision_of_term p)
   else if is_cmpFloatOp_term t then
      let p = dest_cmpFloatOp_term t in
         CmpFloatOp     (float_precision_of_term p)

   else if is_atan2Op_term t then
      let p = dest_atan2Op_term t in
         Atan2Op        (float_precision_of_term p)

   (* Pointer equality *)
   else if is_eqEqOp_term t then
      EqEqOp
   else if is_neqEqOp_term t then
      NeqEqOp

   else
      raise (Invalid_argument "term_to_binop: not a binop")
