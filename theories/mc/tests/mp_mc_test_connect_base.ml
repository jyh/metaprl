(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * A test program to test MC <--> MetaPRL FIR translation code.
 * This module tests "basic" items.
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

(* Open MC namespaces. *)

include Base_theory
open Interval_set
open Rawint
open Rawfloat
open Fir_set
open Fir

(* Open MetaPRL namespaces. *)

open Simple_print.SimplePrint
open Mp_mc_connect_base
open Mp_mc_connect_ty

(* Open ML namespaces. *)

open Printf

(*
 * General functions and variables.
 *)

let fail_count = ref 0
let var1 = Symbol.new_symbol_string "var1"
let var2 = Symbol.new_symbol_string "var2"
let var3 = Symbol.new_symbol_string "var3"
let set1 = IntSet.of_interval (Closed (-3)) (Closed 3)
let set2 = RawIntSet.of_interval
            Int8
            true
            (Closed (Rawint.of_string Int8 true "-3"))
            (Closed (Rawint.of_string Int8 true "3"))

let print_pass () =
   printf "\nTest passes.\n\n"

let print_fail () =
   fail_count := !fail_count + 1;
   printf "\n===> TEST FAILS! <===\n\n"

let rawfloat_test () =
   printf "--> Test: (rawfloat) 3.14159265358979323846264338327950\n";
   let f =
      (Rawfloat.of_string LongDouble "3.14159265358979323846264338327950") in
   let t = number_term_of_rawfloat f in
   let t' = rawfloat_of_number_term LongDouble t in
      print_simple_term t;
      if t' = f then
         print_pass ()
      else
         print_fail ()

let string_test s str =
   printf "--> Test: %s\n" str;
   let t = term_of_string s in
   let t' = string_of_term t in
      print_simple_term t;
      if t' = s then
         print_pass ()
      else
         print_fail ()

let set_test set str =
   printf "--> Test: %s\n" str;
   let t = term_of_set set in
   let t' = set_of_term t in
      print_simple_term t;
      if t' = set then
         print_pass ()
      else
         print_fail ()

(*
 * Define a function to run all the tests.
 *)

let run_tests () =
   fail_count := 0;
   printf "\n\n==> Beginning base tests <==\n\n";

   (* Rawfloats. *)
   rawfloat_test ();

   (* Strings. *)
   string_test "Help!! EEp!" "\"Help!! EEp!\"";

   (* Sets. *)
   set_test (IntSet set1) "[-3,3] (IntSet)";
   set_test (RawIntSet set2) "[-3,3] (RawIntSet)";

   (* Done. *)
   !fail_count
