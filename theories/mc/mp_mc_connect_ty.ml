(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Operations for converting between MC Fir types and MetaPRL terms.
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

open Fir

(* Open MetaPRL ML namespaces. *)

open Refiner.Refiner.RefineError
open Itt_list
open Mp_mc_fir_ty
open Mp_mc_connect_base

(*
 * Convert to and from ty.
 *)

let rec term_of_ty t =
   match t with

      (* Base types. *)
      TyInt ->    tyInt_term
    | TyEnum i -> mk_tyEnum_term (number_term_of_int i)

      (* Native types. *)
    | TyRawInt (p, s) ->
         mk_tyRawInt_term  (term_of_int_precision p) (term_of_int_signed s)
    | TyFloat p ->
         mk_tyFloat_term   (term_of_float_precision p)

      (* Functions. *)
    | TyFun (tyl, t) ->
         mk_tyFun_term  (term_of_list term_of_ty tyl) (term_of_ty t)

      (* Tuples. *)
    | TyUnion (tv, tyl, is) ->
         mk_tyUnion_term (term_of_ty_var tv)
                         (term_of_list term_of_ty tyl)
                         (term_of_int_set is)
    | TyTuple (tc, tyl) ->
         mk_tyTuple_term (term_of_tuple_class tc)
                         (term_of_list term_of_ty tyl)
    | TyArray t ->
         mk_tyArray_term (term_of_ty t)
    | TyRawData ->
         tyRawData_term
    | TyPointer (v, t) ->
         mk_tyPointer_term (term_of_var v)      (term_of_ty t)
    | TyFrame (lbl, t) ->
         mk_tyFrame_term   (term_of_label lbl)  (term_of_ty t)

      (* Polymorphism. *)
    | TyVar tv ->
         mk_tyVar_term     (term_of_ty_var tv)
    | TyApply (tv, tyl) ->
         mk_tyApply_term   (term_of_ty_var tv)
                           (term_of_list term_of_ty tyl)
    | TyExists (tvl,t) ->
         mk_tyExists_term  (term_of_list term_of_ty_var tvl)
                           (term_of_ty t)
    | TyAll (tvl, t) ->
         mk_tyAll_term     (term_of_list term_of_ty_var tvl)
                           (term_of_ty t)
    | TyProject (v,i) ->
         mk_tyProject_term (term_of_var v)
                           (number_term_of_int i)

      (* Object-oriented. *)
    | TyCase t ->
         mk_tyCase_term    (term_of_ty t)
    | TyObject (tv, t) ->
         mk_tyObject_term  (term_of_ty_var tv) (term_of_ty t)
    | TyOption t ->
         mk_tyOption_term  (term_of_ty t)

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

   (* Tuples. *)
   else if is_tyUnion_term t then
      let tv, tyl, s = dest_tyUnion_term t in
         TyUnion (ty_var_of_term tv)
                 (list_of_term ty_of_term tyl)
                 (int_set_of_term s)
   else if is_tyTuple_term t then
      let tc, tyl = dest_tyTuple_term t in
         TyTuple (tuple_class_of_term tc)
                 (list_of_term ty_of_term tyl)
   else if is_tyArray_term t then
      TyArray (ty_of_term (dest_tyArray_term t))
   else if is_tyRawData_term t then
      TyRawData
   else if is_tyPointer_term t then
      let v, t = dest_tyPointer_term t in
         TyPointer (var_of_term v) (ty_of_term t)
   else if is_tyFrame_term t then
      let lbl, t = dest_tyFrame_term t in
         TyFrame (label_of_term lbl) (ty_of_term t)

   (* Polymorphism. *)
   else if is_tyVar_term t then
      TyVar (ty_var_of_term (dest_tyVar_term t))
   else if is_tyApply_term t then
      let tv, tyl = dest_tyApply_term t in
         TyApply (ty_var_of_term tv) (list_of_term ty_of_term tyl)
   else if is_tyExists_term t then
      let tvl, t = dest_tyExists_term t in
         TyExists (list_of_term ty_var_of_term tvl) (ty_of_term t)
   else if is_tyAll_term t then
      let tvl, t = dest_tyAll_term t in
         TyAll (list_of_term ty_var_of_term tvl) (ty_of_term t)
   else if is_tyProject_term t then
      let v, i = dest_tyProject_term t in
         TyProject (var_of_term v) (int_of_number_term i)

   (* Object-oriented. *)
   else if is_tyCase_term t then
      TyCase (ty_of_term (dest_tyCase_term t))
   else if is_tyObject_term t then
      let tv, t = dest_tyObject_term t in
         TyObject (ty_var_of_term tv) (ty_of_term t)
   else if is_tyOption_term t then
      TyOption (ty_of_term (dest_tyOption_term t))

   (* Type should be inferred. *)
   else if is_tyDelayed_term t then
      TyDelayed

   else
      raise (RefineError ("ty_of_term", StringTermError
            ("not a ty", t)))

(*
 * Convert to and from tydef.
 *)

(* Define helper functions. *)

let term_of_ty_bool (t, b) =
   mk_unionElt_term (term_of_ty t) (term_of_bool b)

let ty_bool_of_term t =
   if is_unionElt_term t then
      let t, b = dest_unionElt_term t in
         (ty_of_term t), (bool_of_term b)
   else
      raise (RefineError ("ty_bool_of_term", StringTermError
            ("not an unionElt / (ty, bool)", t)))

let term_of_ty_bool_list_list tbll =
   (term_of_list (term_of_list term_of_ty_bool) tbll)

let ty_bool_list_list_of_term tbll =
   (list_of_term (list_of_term ty_bool_of_term) tbll)

(* Actual functions. *)

let term_of_tydef tyd =
   match tyd with
      TyDefUnion (tvl, ut, tbll) ->
         mk_tyDefUnion_term   (term_of_list term_of_ty_var tvl)
                              (term_of_union_type ut)
                              (term_of_ty_bool_list_list tbll)
    | TyDefLambda (tvl, t) ->
         mk_tyDefLambda_term  (term_of_list term_of_ty_var tvl)
                              (term_of_ty t)

let tydef_of_term t =
   if is_tyDefUnion_term t then
      let tvl, ut, tbll = dest_tyDefUnion_term t in
         TyDefUnion  (list_of_term ty_var_of_term tvl)
                     (union_type_of_term ut)
                     (ty_bool_list_list_of_term tbll)
   else if is_tyDefLambda_term t then
      let tvl, t = dest_tyDefLambda_term t in
         TyDefLambda (list_of_term ty_var_of_term tvl)
                     (ty_of_term t)
   else
      raise (RefineError ("tydef_of_term", StringTermError
            ("not a tydef", t)))
