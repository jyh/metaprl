(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Operations for converting between MC Fir types and MetaPRL terms.
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

open Rawint
open Rawfloat
open Fir

(* Open MetaPRL ML namespaces. *)

open Fir_ty
open Mc_fir_connect_base

(*************************************************************************
 * Convert to and from int_precision, int_signed, and float_precision.
 *************************************************************************)

let term_of_int_precision ip =
   match ip with
      Int8 ->  int8_term
    | Int16 -> int16_term
    | Int32 -> int32_term
    | Int64 -> int64_term

let int_precision_of_term t =
   if is_int8_term t then
      Int8
   else if is_int16_term t then
      Int16
   else if is_int32_term t then
      Int32
   else if is_int64_term t then
      Int64
   else
      raise (Invalid_argument "int_precision_of_term: not an int_precision")

let term_of_int_signed s =
   if s then
      val_true_term
   else
      val_false_term

let int_signed_of_term t =
   if is_val_true_term t then
      true
   else if is_val_false_term t then
      false
   else
      raise (Invalid_argument "int_signed_of_term: not an int_signed")

let term_of_float_precision fp =
   match fp with
      Single ->      floatSingle_term
    | Double ->      floatDouble_term
    | LongDouble ->  floatLongDouble_term

let float_precision_of_term t =
   if is_floatSingle_term t then
      Single
   else if is_floatDouble_term t then
      Double
   else if is_floatLongDouble_term t then
      LongDouble
   else
      raise (Invalid_argument "float_precision_of_term: not a float_precision")

(*************************************************************************
 * Convert toa nd from ty_var.
 *************************************************************************)

(* Just wrappers right now, since ty_var = symbol. *)

let term_of_ty_var = var_term_of_symbol

let ty_var_of_term = symbol_of_var_term

(*************************************************************************
 * Convert to and from ty.
 *************************************************************************)

let rec term_of_ty t =
   match t with

      (* Base types. *)
      TyInt ->    tyInt_term
    | TyEnum i -> mk_tyEnum_term (number_term_of_int i)

      (* Native types. *)
    | TyRawInt (p,s) ->
         mk_tyRawInt_term  (term_of_int_precision p) (term_of_int_signed s)
    | TyFloat p ->
         mk_tyFloat_term   (term_of_float_precision p)

      (* Functions. *)
    | TyFun (tl,t) ->
         mk_tyFun_term  (term_of_list term_of_ty tl) (term_of_ty t)

      (* Type should be inferred. *)
    | TyDelayed -> tyDelayed_term

let rec ty_of_term t =

   (* Base types. *)
   if is_tyInt_term t then
      TyInt
   else if is_tyEnum_term t then
      TyEnum (int_of_number_term (dest_tyEnum_term t))

   (* Native types. *)
   else if is_tyRawInt_term t then
      let p, s = dest_tyRawInt_term t in
         TyRawInt (int_precision_of_term p) (int_signed_of_term s)
   else if is_tyFloat_term t then
      TyFloat (float_precision_of_term (dest_tyFloat_term t))

   (* Funcions. *)
   else if is_tyFun_term t then
      let tl, t = dest_tyFun_term t in
         TyFun (list_of_term ty_of_term tl) (ty_of_term t)

   (* Type should be inferred. *)
   else if is_tyDelayed_term t then
      TyDelayed

   else
      raise (Invalid_argument "ty_of_term: not a ty")

(*************************************************************************
 * Convert to and from union_type.
 *************************************************************************)

let term_of_union_type ut =
   match ut with
      NormalUnion -> normalUnion_term
    | ExnUnion -> exnUnion_term

let union_type_of_term t =
   if is_normalUnion_term t then
      NormalUnion
   else if is_exnUnion_term t then
      ExnUnion
   else
      raise (Invalid_argument "union_type_of_term: not a union_type")
