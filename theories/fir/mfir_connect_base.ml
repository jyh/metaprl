(*
 * Basic operations for converting between the MCC FIR and
 * MetaPRL terms.
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


(**************************************************************************
 * Print out the given term, and then raise a RefineError.
 * func_name is a string that should be the name of the function
 * raising the error.
 **************************************************************************)

let report_error func_name term =
   print_string ("\n\nError encounted in " ^
                 func_name ^ " with:\n");
   Simple_print.SimplePrint.print_simple_term term;
   print_string "\n\n";
   raise (RefineError (func_name, StringTermError
         ("Invalid term structure for this function.", term)))


(**************************************************************************
 * Convert between symbols and terms.  The idea here is to use our own table
 * to go between the string version of the << 'a >> terms and the
 * Symbol.symbol's they represent.
 **************************************************************************)

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
         (*
          * BUG: We want to be able to deal with new symbols that
          * MetaPRL might have created in the process of rewriting
          * terms and applying inference rules.
          *)
         print_string ("\n\nAiee! Mfir_connect_base.symbol_of_string:\n");
         print_string ("No idea what " ^ str ^ " is supposed to be.\n\n");
         raise (Invalid_argument
               ("symbol_of_string: string \"" ^ str ^ "\" not in table."))

let term_of_symbol s =
   mk_var_term (string_of_symbol s)

let symbol_of_term v =
   symbol_of_string (dest_var v)


(**************************************************************************
 * Convert to and from options.
 **************************************************************************)

let term_of_option converter opt_val =
   match opt_val with
      None ->     none_term
    | Some a ->   mk_some_term (converter a)

let option_of_term converter t =
   if is_none_term t then
      None
   else if is_some_term t then
      Some (converter (dest_some_term t))
   else
      report_error "option_of_term" t


(**************************************************************************
 * Convert to and from bool values.
 **************************************************************************)

let term_of_bool b =
   if b then
      true_term
   else
      false_term

let bool_of_term t =
   if is_true_term t then
      true
   else if is_false_term t then
      false
   else
      report_error "bool_of_term" t


(**************************************************************************
 * Convert between (raw) integer and number terms.
 **************************************************************************)

let number_term_of_int i =
   mk_number_term (num_of_int i)

let int_of_number_term t =
   if is_number_term t then
      int_of_num (dest_number_term t)
   else
      report_error "int_of_number_term" t


let number_term_of_rawint r =
   mk_number_term (num_of_string (Rawint.to_string r))

let rawint_of_number_term precision sign t =
   if is_number_term t then
      Rawint.of_string precision sign (string_of_num (dest_number_term t))
   else
      report_error "rawint_of_number_term" t


(**************************************************************************
 * Convert int_precision, int_signed, and float_precision.
 **************************************************************************)

let num_of_int_precision p =
   match p with
      Int8 ->  (num_of_int 8)
    | Int16 -> (num_of_int 16)
    | Int32 -> (num_of_int 32)
    | Int64 -> (num_of_int 64)

let int_precision_of_num n =
   let i = int_of_num n in
      match int_of_num n with
         8 ->  Int8
       | 16 -> Int16
       | 32 -> Int32
       | 64 -> Int64
       | _ ->
            raise (Invalid_argument ("int_precision_of_num: not a rawint precision --- " ^ (string_of_int i)))


let string_of_int_signed s =
   if s then
      "signed"
   else
      "unsigned"

let int_signed_of_string s =
   if s = "signed" then
      true
   else if s = "unsigned" then
      false
   else
      raise (Invalid_argument ("int_signed_of_string: not a int_signed --- " ^ s))


let num_of_float_precision p =
   match p with
      Single ->      (num_of_int 32)
    | Double ->      (num_of_int 64)
    | LongDouble ->  (num_of_int 80)

let float_precision_of_num n =
   let i = int_of_num n in
      match int_of_num n with
         32 -> Single
       | 64 -> Double
       | 80 -> Double
       | _ ->
            raise (Invalid_argument ("float_precision_of_num: not a float_precision --- " ^ (string_of_int i)))


(**************************************************************************
 * Convert a list to a "term list", i.e. << cons{ ... } >>.
 **************************************************************************)

let rec term_of_list converter l =
   match l with
      [] ->
         nil_term
    | h :: t ->
         let h' = converter h in
         let t' = term_of_list converter t in
            mk_cons_term h' t'

let rec list_of_term converter t =
   if is_cons_term t then
      let head, tail = dest_cons_term t in
      let tail' = list_of_term converter tail in
      let head' = converter head in
         head' :: tail'
   else if t = nil_term then
      []
   else
      report_error "list_of_term" t


(**************************************************************************
 * Convert (raw) integer sets to terms.  Integers and raw integers must
 * be treated seperately in the functions below.
 **************************************************************************)

(*
 * Convert bounds to and from number terms.
 *)

let term_of_int_bound b =
   match b with
      Closed i ->
         number_term_of_int i
    | _ ->
         raise (Invalid_argument "term_of_int_bound: not a Closed bound")

let int_bound_of_term t =
   if is_number_term t then
      Closed (int_of_number_term t)
   else
      report_error "int_bound_of_term" t


let term_of_rawint_bound b =
   match b with
      Closed r ->
         number_term_of_rawint r
    | _ ->
         raise (Invalid_argument "term_of_rawint_bound: not a Closed bound")

let rawint_bound_of_term precision sign t =
   if is_number_term t then
      Closed (rawint_of_number_term precision sign t)
   else
      report_error "rawint_bound_of_term" t


(*
 * The two functions below take a term and the bounds of an interval.
 * They create a new cons term with the interval as the head and the
 * given term as the tail.
 *)

let fold_intset term left right =
   let left' = term_of_int_bound left in
   let right' = term_of_int_bound right in
   let interval = mk_interval_term left' right' in
      mk_cons_term interval term

let fold_rawintset term left right =
   let left' = term_of_rawint_bound left in
   let right' = term_of_rawint_bound right in
   let interval = mk_interval_term left' right' in
      mk_cons_term interval term


(*
 * The two functions below are almost the inverses of the above
 * two folding functions.  The take a list of intervals (as a term)
 * and union them with the given (raw) integer set.
 *)

let rec unfold_intset set intervals =
   if is_cons_term intervals then
      let head, tail = dest_cons_term intervals in
         if is_interval_term head then
            let left, right = dest_interval_term head in
            let left' = int_of_number_term left in
            let right' = int_of_number_term right in
            let newset = IntSet.of_interval (Closed left') (Closed right') in
               unfold_intset (IntSet.union newset set) tail
         else
            report_error "unfold_intset (head)" intervals
   else if is_nil_term intervals then
      set
   else
      report_error "unfold_intset" intervals

let rec unfold_rawintset precision sign set intervals =
   if is_cons_term intervals then
      let head, tail = dest_cons_term intervals in
         if is_interval_term head then
            let left, right = dest_interval_term head in
            let left' = rawint_of_number_term precision sign left in
            let right' = rawint_of_number_term precision sign right in
            let newset = RawIntSet.of_interval precision sign (Closed left') (Closed right') in
               unfold_rawintset precision sign (RawIntSet.union newset set) tail
         else
            report_error "unfold_rawintset (head)" intervals
   else if is_nil_term intervals then
      set
   else
      report_error "unfold_rawintset" intervals


(*
 * The main functions for converting between integer sets and terms
 * use the folding and unfolding functions above to perform most of
 * the work.
 *)

let term_of_int_set set =
   mk_intset_term (num_of_int 31)
                  "signed"
                  (IntSet.fold fold_intset nil_term set)

let int_set_of_term t =
   if is_intset_term t then
      let precision, sign, intervals = dest_intset_term t in
         if 31 = (int_of_num precision) && (int_signed_of_string sign) then
            unfold_intset IntSet.empty intervals
         else
            report_error "int_set_of_term (inner)" t
   else
      report_error "int_set_of_term" t


let term_of_rawint_set set =
   mk_intset_term (num_of_int_precision (RawIntSet.precision set))
                  (string_of_int_signed (RawIntSet.signed set))
                  (RawIntSet.fold fold_rawintset nil_term set)

let rawint_set_of_term t =
   if is_intset_term t then
      let precision, sign, intervals = dest_intset_term t in
         try
            let precision' = int_precision_of_num precision in
            let sign' = int_signed_of_string sign in
               unfold_rawintset precision' sign' (RawIntSet.empty precision' sign') intervals
         with
            _ -> report_error "rawint_set_of_term (inner)" t
   else
      report_error "rawint_set_of_term" t


let term_of_set s =
   match s with
      IntSet i ->    term_of_int_set i
    | RawIntSet r -> term_of_rawint_set r

let set_of_term t =
   if is_intset_term t then
      let precision, _, _ = dest_intset_term t in
         if 31 = (int_of_num precision) then
            IntSet (int_set_of_term t)
         else
            RawIntSet (rawint_set_of_term t)
   else
      report_error "set_of_term" t
