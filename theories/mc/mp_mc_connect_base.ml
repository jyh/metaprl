(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Basic operations for converting between the MCC FIR and
 * MetaPRL terms.
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
open Itt_atom
open Itt_int_base
open Itt_list
open Mp_mc_fir_base

(*
 * Print out the given term, and then raise a RefineError.
 * func_name is a string that should be the name of the function
 * raising the error.
 *)

let report_error func_name term =
   print_string ("\n\nError encounted in " ^
                 func_name ^ " with:\n");
   Simple_print.SimplePrint.print_simple_term term;
   print_string "\n\n";
   raise (RefineError (func_name, StringTermError
         ("Invalid term structure for this function.", term)))

(*************************************************************************
 * Basic conversions.
 *************************************************************************)

(*
 * Convert between var's, ty_var's, label's, and terms.
 * The idea here is to use our own table to go between the string
 * version of the << 'a >> terms and the Symbol.symbol's they represent.
 *)

let table = Hashtbl.create 128

let string_of_symbol sym =
   let str = Symbol.string_of_symbol sym in
      Hashtbl.add table str sym;
      str

let symbol_of_string str =
   try
      Hashtbl.find table str
   with
      Not_found ->
         raise (Invalid_argument
               ("symbol_of_string: string \"" ^ str ^ "\" not in table."))

let var_term_of_symbol s =
   mk_var_term (string_of_symbol s)

let symbol_of_var_term v =
   try
      symbol_of_string (dest_var v)
   with
      Not_found ->
         raise (Invalid_argument "can't create symbols out of thin air yet")

(* Alias the below functions to keep the interface as general as possible. *)

let term_of_symbol = var_term_of_symbol
let symbol_of_term = symbol_of_var_term

let term_of_var = var_term_of_symbol
let var_of_term = symbol_of_var_term
let string_of_var = string_of_symbol
let var_of_string = symbol_of_string

let term_of_ty_var = var_term_of_symbol
let ty_var_of_term = symbol_of_var_term
let string_of_ty_var = string_of_symbol
let ty_var_of_string = symbol_of_string

let term_of_label = var_term_of_symbol
let label_of_term = symbol_of_var_term
let string_of_label = string_of_symbol
let label_of_string = symbol_of_string

(*
 * Convert between integer constants and numbers.
 *)

let number_term_of_int i =
   mk_number_term (num_of_int i)

let int_of_number_term n =
   int_of_num (dest_number n)

let number_term_of_rawint r =
   mk_number_term (num_of_string (Rawint.to_string r))

let rawint_of_number_term precision sign t =
   Rawint.of_string precision sign (string_of_num (dest_number t))

let number_term_of_rawfloat f =
   mk_token_term (Rawfloat.to_string f)

let rawfloat_of_number_term precision t =
   Rawfloat.of_string precision (dest_token t)

(*
 * Convert to and from string values.
 *)

let term_of_string str =
   mk_token_term str

let string_of_term t =
   if is_token_term t then
      dest_token t
   else
      report_error "string_of_term" t

(*
 * Convert a list to a "term list", i.e. << cons{ ... } >>.
 *)

let rec term_of_list f l =
   match l with
      [] ->
         nil_term
    | h :: t ->
         let h' = f h in
         let t' = term_of_list f t in
            mk_cons_term h' t'

let rec list_of_term f_conv t =
   if is_cons_term t then
      let head, tail = dest_cons t in
      let tail' = list_of_term f_conv tail in
      let head' = f_conv head in
         head' :: tail'
   else if t = nil_term then
      []
   else
      report_error "list_of_term" t

(*
 * Convert SymbolTable's to terms.
 *)

(* Creates a tableItem term given conversion functions to convert
 * the key and value given to terms. *)

let term_of_table_item key_converter value_converter key value =
   mk_tableItem_term (key_converter    key)
                     (value_converter  value)

(* Takes a tableItem term and returns the (key,value) table entry
 * that it represents. *)

let table_item_of_term key_converter value_converter term =
   if is_tableItem_term term then
      let key, value = dest_tableItem_term term in
         key_converter key, value_converter value
   else
      report_error "table_item_of_term" term

(* Used to fold together a list term for a SymbolTable. *)

let symbol_table_folder value_converter term_list key value =
   mk_cons_term (term_of_table_item term_of_symbol value_converter key value)
                term_list

(* Unfolds a list term into a SymbolTable. *)

let rec unfold_symbol_table_term existing_table converter term =
   if is_cons_term term then
      let head, tail = dest_cons term in
      let key, value = table_item_of_term symbol_of_term converter term in
         unfold_symbol_table_term
            (SymbolTable.add existing_table key value)
            converter
            tail
   else if term = nil_term then
      existing_table
   else
      report_error "unfold_symbol_table_term" term

(* Makes a list term out of a SymbolTable, given a function to convert
 * the values in the table and the table itself. *)

let term_of_symbol_table value_converter table =
   SymbolTable.fold (symbol_table_folder value_converter) nil_term table

(* Takes a list term and creates a SymbolTable out of it,
 * given a function to convert the values of the table and the list term. *)

let symbol_table_of_term converter term =
   try
      unfold_symbol_table_term SymbolTable.empty converter term
   with
      _ -> report_error "symbol_table_of_term" term

(*************************************************************************
 * Conversions for terms in Mp_mc_fir_base.
 *************************************************************************)

(*
 * Convert to and from options.
 *)

let term_of_option converter opt_val =
   match opt_val with
      None ->     noneOpt_term
    | Some a ->   mk_someOpt_term (converter a)

let option_of_term converter t =
   if is_noneOpt_term t then
      None
   else if is_someOpt_term t then
      Some (converter (dest_someOpt_term t))
   else
      report_error "option_of_term" t

(*
 * Convert to and from bool values.
 *)

let term_of_bool b =
   if b then
      val_true_term
   else
      val_false_term

let bool_of_term t =
   if is_val_true_term t then
      true
   else if is_val_false_term t then
      false
   else
      report_error "bool_of_term" t

(*
 * Convert to and from int_precision and float_precision.
 *)

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
      report_error "int_precision_of_term" t

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
      report_error "float_precision_of_term" t

(*
 * Convert to and from int_signed.
 *)

let term_of_int_signed is =
   if is then
      signedInt_term
   else
      unsignedInt_term

let int_signed_of_term t =
   if is_signedInt_term t then
      true
   else if is_unsignedInt_term t then
      false
   else
      report_error "int_signed_of_term" t

(*
 * Convert to and from int_set, rawint_set, and set.
 *)

(* Convert bounds.  I assume that they're always closed. *)

let number_term_of_int_bound b =
   match b with
      Closed i -> number_term_of_int i
    | _ -> raise (Invalid_argument
                  "number_term_of_int_bound: not a closed int bound")

let bound_of_int_number_term t =
   Closed (int_of_number_term t)

let number_term_of_raw_bound b =
   match b with
      Closed r -> number_term_of_rawint r
    | _ -> raise (Invalid_argument
                  "number_term_of_raw_bound: not a closed rawint bound")

let bound_of_raw_number_term precision sign t =
   Closed (rawint_of_number_term precision sign t)

(* Here, we're given something like cons{ interval{'l;'r}; ... }.
   We turn this into a list [('l,'r); ...]. *)

let rec extract_intervals_as_number_pairs intervals =
   if is_cons_term intervals then
      let head, tail = dest_cons intervals in
         (dest_interval_term head) :: (extract_intervals_as_number_pairs tail)
   else if intervals = nil_term then
      []
   else
      raise (Invalid_argument
             "extract_intervals_as_number_pairs: not a \"list\" term")

(* Folding functions to be used below. *)

let int_interval_folder existing_set (left, right) =
   IntSet.union existing_set
                (IntSet.of_interval (bound_of_int_number_term left)
                                    (bound_of_int_number_term right))

let rawint_interval_folder p s existing_set (left, right) =
   RawIntSet.union existing_set
                    (RawIntSet.of_interval
                              p
                              s
                              (bound_of_raw_number_term p s left)
                              (bound_of_raw_number_term p s right))

(* Here, we're given something like cons{ interval{'l;'r}; ... }.
   We use the folding function and "interval extraction" functions above
   to make a new set. *)

let intSet_of_intervals i =
   List.fold_left int_interval_folder
                  IntSet.empty
                  (extract_intervals_as_number_pairs i)

let rawIntSet_of_intervals precision sign i =
   List.fold_left (rawint_interval_folder precision sign)
                  (RawIntSet.empty precision sign)
                  (extract_intervals_as_number_pairs i)

(* Actual conversion functions for the sets. The idea is to turn each
   interval into an interval term, and vica versa (see above functions). *)

let term_of_int_set s =
   mk_int_set_term
      (IntSet.fold
         (fun tail left right ->
            mk_cons_term
               (mk_interval_term
                  (number_term_of_int_bound left)
                  (number_term_of_int_bound right))
               tail)
         nil_term
         s)

let int_set_of_term t =
   if is_int_set_term t then
      intSet_of_intervals (dest_int_set_term t)
   else
      report_error "int_set_of_term" t

let term_of_rawint_set s =
   let intervals_term_list =
      (RawIntSet.fold
         (fun tail left right ->
            mk_cons_term
               (mk_interval_term
                  (number_term_of_raw_bound left)
                  (number_term_of_raw_bound right)
               )
               tail
         )
         nil_term
         s
      )
   in
      mk_rawint_set_term (term_of_int_precision (RawIntSet.precision s))
                         (term_of_int_signed (RawIntSet.signed s))
                         intervals_term_list

let rawint_set_of_term t =
   if is_rawint_set_term t then
      let precision, sign, intervals = dest_rawint_set_term t in
         rawIntSet_of_intervals (int_precision_of_term precision)
                                (int_signed_of_term sign)
                                intervals
   else
      report_error "rawint_set_of_term" t

let term_of_set s =
   match s with
      IntSet i ->    term_of_int_set i
    | RawIntSet r -> term_of_rawint_set r

let set_of_term t =
   if is_int_set_term t then
      IntSet (int_set_of_term t)
   else if is_rawint_set_term t then
      RawIntSet (rawint_set_of_term t)
   else
      report_error "set_of_term" t

(*
 * Convert to and from tuple_class.
 *)

let term_of_tuple_class tc =
   match tc with
      NormalTuple -> normalTuple_term
    | RawTuple    -> rawTuple_term

let tuple_class_of_term t =
   if is_normalTuple_term t then
      NormalTuple
   else if is_rawTuple_term t then
      RawTuple
   else
      report_error "tuple_class_of_term" t

(*
 * Convert to and from union_type.
 *)

let term_of_union_type ut =
   match ut with
      NormalUnion -> normalUnion_term
    | ExnUnion    -> exnUnion_term

let union_type_of_term t =
   if is_normalUnion_term t then
      NormalUnion
   else if is_exnUnion_term t then
      ExnUnion
   else
      report_error "union_type_of_term" t

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
      report_error "sub_block_of_term" t

let term_of_sub_value v =
   match v with
      PolySub ->           polySub_term
    | RawIntSub (p, s) ->  mk_rawIntSub_term (term_of_int_precision p)
                                             (term_of_int_signed s)
    | RawFloatSub p ->     mk_rawFloatSub_term (term_of_float_precision p)
    | PointerInfixSub ->   pointerInfixSub_term
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
   else if is_pointerInfixSub_term t then
      PointerInfixSub
   else if is_pointerSub_term t then
      PointerSub
   else if is_functionSub_term t then
      FunctionSub
   else
      report_error "sub_value_of_term" t

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
      report_error "sub_index_of_term" t

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
      report_error "sub_script_of_term" t

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
      report_error "subop_of_term" t
