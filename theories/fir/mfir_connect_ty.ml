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

open Symbol
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
         (*
          * BUG: if tyl = [] then this case does NOT return a tyFun term.
          *)
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


(**************************************************************************
 * Convert to mutable_flag and mutable_ty.
 **************************************************************************)

let mutable_flag_of_term t =
   if is_mutable_term t then
      Mutable
   else if is_immutable_term t then
      Immutable
   else
      report_error "mutable_flag_of_term" t


let rec mutable_ty_of_term t =
   if is_mutable_ty_term t then
      let ty, flag = dest_mutable_ty_term t in
         ty_of_term ty, mutable_flag_of_term flag
   else
      report_error "mutable_ty_of_term" t


(**************************************************************************
 * Convert to ty.
 **************************************************************************)

and ty_of_term t =

   (* Numbers. *)
   if is_tyInt_term t then
      TyInt
   else if is_tyEnum_term t then
      let n = dest_tyEnum_term t in
         TyEnum (int_of_num n)
   else if is_tyRawInt_term t then
      let p, s = dest_tyRawInt_term t in
         TyRawInt (int_precision_of_num p) (int_signed_of_string s)
   else if is_tyFloat_term t then
      let p = dest_tyFloat_term t in
         TyFloat (float_precision_of_num p)

   (* Functions. *)
   else if is_tyFun_term t then
      let rec tyFun_of_term tyl t =
         if not (is_tyFun_term t) then
            TyFun (tyl, ty_of_term t)
         else
            let arg, res = dest_tyFun_term t in
               tyFun_of_term (tyl @ [ty_of_term arg]) res
      in
         tyFun_of_term [] t

   (* Tuples. *)
   else if is_tyUnion_term t then
      let tv, tyl, is = dest_tyUnion_term t in
         TyUnion  (symbol_of_term tv)
                  (list_of_term ty_of_term tyl)
                  (int_set_of_term is)
   else if is_tyTuple_term t then
      let tuple_class_of_string tc =
         if tc = "normal" then
            NormalTuple
         else if tc = "raw" then
            RawTuple
         else if tc = "box" then
            BoxTuple
         else
            report_error "ty_of_term" t
      in
         let tc, mtyl = dest_tyTuple_term t in
            TyTuple  (tuple_class_of_string tc)
                     (list_of_term mutable_ty_of_term mtyl)
   else if is_tyDTuple_term t then
      let tv, mtyl_opt = dest_tyDTuple_term t in
         TyDTuple (symbol_of_term tv)
                  (option_of_term (list_of_term mutable_ty_of_term) mtyl_opt)
   else if is_tyTag_term t then
      let tv, mtyl = dest_tyTag_term t in
         TyTag (symbol_of_term tv) (list_of_term mutable_ty_of_term mtyl)

   (* Other aggregates. *)
   else if is_tyArray_term t then
      let ty = dest_tyArray_term t in
         TyArray (ty_of_term ty)
   else if is_tyRawData_term t then
      TyRawData
   else if is_tyFrame_term t then
      let tv, tyl = dest_tyFrame_term t in
         TyFrame (symbol_of_term tv) (list_of_term ty_of_term tyl)

   (* Polymorphism. *)
   else if is_tyVar_term t then
      let tv = dest_tyVar_term t in
         TyVar (symbol_of_term tv)
   else if is_tyApply_term t then
      let tv, tyl = dest_tyApply_term t in
         TyApply (symbol_of_term tv) (list_of_term ty_of_term tyl)
   else if is_tyExists_term t then
      let rec tyExists_of_term tyl t =
         if is_tyExists_term t then
            let v, ty = dest_tyExists_term t in
               tyExists_of_term (tyl @ [symbol_of_string v]) ty
         else
            TyExists (tyl, ty_of_term t)
      in
         tyExists_of_term [] t
   else if is_tyAll_term t then
      let rec tyAll_of_term tyl t =
         if is_tyAll_term t then
            let v, ty = dest_tyAll_term t in
               tyAll_of_term (tyl @ [symbol_of_string v]) ty
         else
            TyAll (tyl, ty_of_term t)
      in
         tyAll_of_term [] t
   else if is_tyProject_term t then
      let n, v = dest_tyProject_term t in
         TyProject (symbol_of_term v) (int_of_num n)

   (* Terms that are not handled. *)
   else
      report_error "ty_of_term" t


(**************************************************************************
 * Convert to and from tydef.
 **************************************************************************)

let term_of_tydef tyd =
   match tyd with
      TyDefUnion (tvl, mtyll) ->
         let rec process_lambda tvl mtyll =
            match tvl with
               [] ->
                  mk_tyDefUnion_term (term_of_list (term_of_list term_of_mutable_ty) mtyll)
             | h :: t ->
                  mk_tyDefPoly_term (string_of_symbol h)
                                    (process_lambda t mtyll)
         in
            process_lambda tvl mtyll
    | TyDefLambda (tvl, ty) ->
         let rec process_lambda tvl ty =
            match tvl with
               [] ->
                  term_of_ty ty
             | h :: t ->
                  mk_tyDefPoly_term (string_of_symbol h)
                                    (process_lambda t ty)
         in
            process_lambda tvl ty
    | TyDefDTuple tv ->
         mk_tyDefDTuple_term  (term_of_symbol tv)


(*
 * Deconstructing tydef terms involves determining the ``core''
 * of a tyDefPoly term, potentially.
 *)

let rec process_polydef vars t =
   if is_tyDefPoly_term t then
      let v, ty = dest_tyDefPoly_term t in
         process_polydef (vars @ [symbol_of_string v]) ty
   else if is_tyDefUnion_term t then
      let mtyll = dest_tyDefUnion_term t in
         TyDefUnion (vars, list_of_term (list_of_term mutable_ty_of_term) mtyll)
   else if is_tyDefDTuple_term t then
      let tv = dest_tyDefDTuple_term t in
         TyDefDTuple (symbol_of_term tv)
   else
      TyDefLambda (vars, ty_of_term t)

let tydef_of_term t =
   process_polydef [] t


(**************************************************************************
 * Convert to and from frame.
 **************************************************************************)

(*
 * The real work of converting frames requires going between a record
 * (see Mfir_record) and a ((var * ty * int) list) SymbolTable.t.
 *)

(* Append a (var * ty * int) list to the given record. *)

let rec term_of_frame_field rcrd f =
   match f with
      [] ->
         rcrd
    | (v, ty, i) :: t ->
         let subfield_term = mk_frameSubField_term (term_of_ty ty)
                                                   (number_term_of_int i)
         in
         let new_rcrd = mk_record_term (string_of_symbol v)
                                       subfield_term
                                       rcrd
         in
            term_of_frame_field new_rcrd t

(* Turn a record into a (var * ty * int) list. *)

let rec frame_field_of_term lst t =
   if is_recordEnd_term t then
      lst
   else if is_record_term t then
      let var, data, rest = dest_record_term t in
         if is_frameSubField_term data then
            let ty, i = dest_frameSubField_term data in
            let new_list = ( symbol_of_string var,
                             ty_of_term ty,
                             int_of_number_term i ) :: lst in
               frame_field_of_term new_list rest
         else
            report_error "frame_field_of_term" t
   else
      report_error "frame_field_of_term" t


(*
 * The above functions make the actual frame conversion
 * rather straightforward.
 *)

(* Go from a frame to a term. *)

let term_of_core_frame f =
   let fold_func rcrd key value =
      let frame_field = term_of_frame_field recordEnd_term value in
      let new_record = mk_record_term (string_of_symbol key)
                                      frame_field
                                      rcrd
      in
         new_record
   in
      SymbolTable.fold fold_func recordEnd_term f

let rec term_of_frame (vars, f) =
   match vars with
      [] ->
         term_of_core_frame f
    | h :: t ->
         mk_tyDefPoly_term (string_of_symbol h)
                           (term_of_frame (t, f))

(* Go from a term to a frame. *)

let rec build_table tbl t =
   if is_recordEnd_term t then
      tbl
   else if is_record_term t then
      let var, data, rest = dest_record_term t in
      let field = frame_field_of_term [] data in
      let new_tbl = SymbolTable.add tbl (symbol_of_string var) field in
         build_table new_tbl rest
   else
      report_error "build_table (frame_of_term)" t

let rec build_vars vars t =
   if is_tyDefPoly_term t then
      let v, ty = dest_tyDefPoly_term t in
         build_vars (vars @ [symbol_of_string v]) ty
   else
      vars, build_table SymbolTable.empty t

let frame_of_term t =
   if is_tyDefPoly_term t then
      build_vars [] t
   else if is_record_term t then
      [], build_table SymbolTable.empty t
   else
      report_error "frame_of_term" t
