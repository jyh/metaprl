(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Basic operations for converting between the MC Fir and
 * MetaPRL terms.
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
open Itt_int_base
open Itt_list
open Mc_set
open Fir_ty

(*************************************************************************
 * Convert between symbols and variable terms (e.g. 'a).
 *************************************************************************)

let var_term_of_symbol s =
   mk_var_term (string_of_symbol s)

let symbol_of_var_term v =
   new_symbol_string (dest_var v)

(*************************************************************************
 * Convert between integer constants and numbers.
 *************************************************************************)

let number_term_of_int i =
   mk_number_term (num_of_int i)

let int_of_number_term n =
   int_of_num (dest_number n)

let number_term_of_rawint r =
   mk_number_term (num_of_string (Rawint.to_string r))

let rawint_of_number_term precision sign t =
   Rawint.of_string precision sign (string_of_num (dest_number t))

let number_term_of_rawfloat f =
   mk_number_term (num_of_string (Rawfloat.to_string f))

let rawfloat_of_number_term p t =
   Rawfloat.of_string p (string_of_num (dest_number t))

(*************************************************************************
 * Convert to and from bool values.
 *************************************************************************)

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
      raise (RefineError ("term_of_bool", StringTermError
            ("not a bool", t)))

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
      raise (RefineError ("term_of_int_precision", StringTermError
            ("not an int_precision", t)))

(* Wrappers as long as int_signed = bool. *)

let term_of_int_signed = term_of_bool

let int_signed_of_term = bool_of_term

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
      raise (RefineError ("float_precision_of_term", StringTermError
            ("not a float_precision", t)))

(*************************************************************************
 * Conver to and from int_set, rawint_set, and set.
 *************************************************************************)

(*
 * Deal with bounds.  I assume that they're always closed.
 *)

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

let bound_of_raw_number_term t =
   Closed (rawint_of_number_term t)

let precision_of_rawint_bound b =
   match b with
      Closed r -> Rawint.precision r
    | _ -> raise (Invalid_argument
                  "precision_of_rawint_bound: not a closed rawint bound")

let sign_of_rawint_bound b =
   match b with
      Closed r -> Rawint.signed r
    | _ -> raise (Invalid_argument
                  "sign_of_rawint_bound: not a closed rawint bound")

(*
 * Deconstruct intervals.
 *)

let intSet_of_intervals i =
   let intset = IntSet.empty in
      intset

let rawIntSet_of_intervals precision sign i =
   let rawintset = RawIntSet.empty precision sign in
      rawintset

(*
 * Actual conversion functions for the sets.
 *)

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
      raise (RefineError ("int_set_of_term", StringTermError
                         ("not an int_set", t)))

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
      raise (RefineError ("rawint_set_of_term", StringTermError
                         ("not a rawint_set", t)))

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
      raise (RefineError ("set_of_term", StringTermError
            ("not a set", t)))

(*************************************************************************
 * Convert a list to a "term list", i.e. << cons{ ... } >>.
 *************************************************************************)

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
      raise (RefineError ("list_of_term", StringTermError
            ("not a term representing a list", t)))
