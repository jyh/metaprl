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

open Rawint
open Symbol
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

let int_of_number_term n =
   int_of_num (dest_number_term n)

let number_term_of_rawint r =
   mk_number_term (num_of_string (Rawint.to_string r))

let rawint_of_number_term precision sign t =
   Rawint.of_string precision sign (string_of_num (dest_number_term t))


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
      raise (RefineError ("list_of_term", StringTermError
            ("not a list term", t)))
