(*
 * Basic operations for converting MCC FIR types to/from MetaPRL terms.
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

open Fir

(* Open MetaPRL ML namespaces. *)

open Mp_num
open Mfir_termOp
open Mfir_connect_base


(**************************************************************************
 * Convert from mutable_flag and mutable_ty.
 **************************************************************************)

let term_of_mutable_flag flag =
   match flag with
      Mutable ->     mutable_term
    | Immutable ->   immutable_term
    | _ ->
         raise (Invalid_argument "term_of_mutable_flag: given non-trivial flag")


let rec term_of_mutable_ty (ty, flag) =
   mk_mutable_ty_term (term_of_ty ty) (term_of_mutable_flag flag)


(**************************************************************************
 * Convert from ty.
 **************************************************************************)

and term_of_ty t =
   match t with

      (* Numbers. *)
      TyInt ->
         tyInt_term
    | TyEnum i ->
         mk_tyEnum_term    (num_of_int i)
    | TyRawInt (p, s) ->
         mk_tyRawInt_term  (num_of_int_precision p) (string_of_int_signed s)
    | TyFloat p ->
         mk_tyFloat_term   (num_of_float_precision p)

      (* Functions. *)
    | TyFun (tyl, ty) ->
         let rec term_of_tyFun args res =
            match args with
               [] ->       term_of_ty res
             | h :: t ->   mk_tyFun_term (term_of_ty h) (term_of_tyFun t res)
         in
            term_of_tyFun tyl ty

      (* Tuples. *)
    | TyUnion (tv, tyl, is) ->
         mk_tyUnion_term (term_of_symbol tv)
                         (term_of_list term_of_ty tyl)
                         (term_of_int_set is)
    | TyTuple (tc, mtyl) ->
         let string_of_tuple_class tc =
            match tc with
               NormalTuple -> "normal"
             | RawTuple ->    "raw"
             | BoxTuple ->    "box"
         in
            mk_tyTuple_term (string_of_tuple_class tc)
                            (term_of_list term_of_mutable_ty mtyl)
    | TyDTuple (tv, mtyl_option) ->
         mk_tyDTuple_term  (term_of_symbol tv)
                           (term_of_option (term_of_list term_of_mutable_ty) mtyl_option)
    | TyTag (tv, mtyl) ->
         mk_tyTag_term  (term_of_symbol tv)
                        (term_of_list term_of_mutable_ty mtyl)

      (* Other aggregates. *)
    | TyArray t ->
         mk_tyArray_term   (term_of_ty t)
    | TyRawData ->
         tyRawData_term
    | TyFrame (tv, tyl) ->
         mk_tyFrame_term   (term_of_symbol tv)
                           (term_of_list term_of_ty tyl)

      (* Polymorphism. *)
    | TyVar tv ->
         mk_tyVar_term     (term_of_symbol tv)
    | TyApply (tv, tyl) ->
         mk_tyApply_term   (term_of_symbol tv)
                           (term_of_list term_of_ty tyl)
    | TyExists (tyl, ty) ->
         let rec term_of_tyExists args res =
            match args with
               [] ->       term_of_ty res
             | h :: t ->   mk_tyExists_term (string_of_symbol h) (term_of_tyExists t res)
         in
            term_of_tyExists tyl ty
    | TyAll (tyl, ty) ->
         let rec term_of_tyAll args res =
            match args with
               [] ->       term_of_ty res
             | h :: t ->   mk_tyAll_term (string_of_symbol h) (term_of_tyAll t res)
         in
            term_of_tyAll tyl ty
    | TyProject (v,i) ->
         mk_tyProject_term (num_of_int i)
                           (term_of_symbol v)

      (* Types that are not handled. *)
    | TyPointer _
    | TyObject (_, _)
    | TyCase _
    | TyDelayed ->
         raise (Invalid_argument "term_of_ty: unsupported type")
