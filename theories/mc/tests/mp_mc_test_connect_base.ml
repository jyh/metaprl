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

(* Make someone happy... *)

include Base_theory

(* Open MC namespaces. *)

open Rawint
open Rawfloat
open Fir

(* Open MetaPRL namespaces. *)

open Mp_mc_connect_base
open Simple_print.SimplePrint

(* Open ML namespaces. *)

open Printf

(* General functions. *)

let print_head name fir_obj =
   printf "test_%s:\n%s\n" name fir_obj

let print_pass () =
   printf "\nTest passes.\n\n"

let fail_count = ref 0

let print_fail () =
   fail_count := !fail_count + 1;
   printf "\n===> TEST FAILS! <===\n\n"

(*************************************************************************
 * Define test functions.
 *************************************************************************)

(*
 * Integer constants and numbers.
 *)

let test_int () =
   print_head "int" "23415 (integer constant)";
   let t = number_term_of_int 23415 in
   let t' = int_of_number_term t in
      print_simple_term t;
      if t' = 23415 then
         print_pass ()
      else
         print_fail ()

let test_rawint () =
   print_head "rawint" "68719476736 (2^36)";
   let num = Rawint.of_string Int64 false "68719476736" in
   let t = number_term_of_rawint num in
   let t' = rawint_of_number_term Int64 false t in
      print_simple_term t;
      if (Rawint.compare num t') = 0 then
         print_pass ()
      else
         print_fail ()

let test_rawfloat () =
   print_head "rawfloat" "2345.65134";
   let num = Rawfloat.of_string LongDouble "2345.65134" in
   let t = number_term_of_rawfloat num in
   let t' = rawfloat_of_number_term LongDouble t in
      print_simple_term t;
      if (Rawfloat.compare num t') = 0 then
         print_pass ()
      else
         print_fail ()

(*
 * Boolean values.
 *)

let test_val_true () =
   print_head "val_true" "true (ocaml built-in)";
   let t = term_of_bool true in
   let t' = bool_of_term t in
      print_simple_term t;
      if t' then
         print_pass ()
      else
         print_fail ()

let test_val_false () =
   print_head "val_false" "false (ocaml built-in)";
   let t = term_of_bool false in
   let t' = bool_of_term t in
      print_simple_term t;
      if not t' then
         print_pass ()
      else
         print_fail ()

(*
 * String values.
 *)

let test_string () =
   print_head "string" "\"Hallo! This is a test!\"";
   let t = term_of_string "\"Hallo! This is a test!\"" in
   let t' = string_of_term t in
      print_simple_term t;
      Printf.printf "\nterm -> string conversion gives:\n%s\n\n" t';
      if t' = "\"Hallo! This is a test!\"" then
         print_pass ()
      else
         print_fail ()

(*
 * int_precision, int_signed, and float_precision tests.
 *)

let test_int8 () =
   print_head "int8" "Int8";
   let t = term_of_int_precision Int8 in
   let t' = int_precision_of_term t in
      print_simple_term t;
      match t' with
         Int8  -> print_pass ()
       | _     -> print_fail ()

let test_int16 () =
   print_head "int16" "Int16";
   let t = term_of_int_precision Int16 in
   let t' = int_precision_of_term t in
      print_simple_term t;
      match t' with
         Int16 -> print_pass ()
       | _     -> print_fail ()

let test_int32 () =
   print_head "int32" "Int32";
   let t = term_of_int_precision Int32 in
   let t' = int_precision_of_term t in
      print_simple_term t;
      match t' with
         Int32 -> print_pass ()
       | _     -> print_fail ()

let test_int64 () =
   print_head "int64" "Int64";
   let t = term_of_int_precision Int64 in
   let t' = int_precision_of_term t in
      print_simple_term t;
      match t' with
         Int64 -> print_pass ()
       | _     -> print_fail ()

let test_int_signed_true () =
   print_head "int_signed_true" "true (ocaml built-in)";
   let t = term_of_bool true in
   let t' = bool_of_term t in
      print_simple_term t;
      if t' then
         print_pass ()
      else
         print_fail ()

let test_int_signed_false () =
   print_head "int_signed_false" "false (ocaml built-in)";
   let t = term_of_int_signed false in
   let t' = int_signed_of_term t in
      print_simple_term t;
      if not t' then
         print_pass ()
      else
         print_fail ()

let test_floatSingle () =
   print_head "floatSingle" "Single";
   let t = term_of_float_precision Single in
   let t' = float_precision_of_term t in
      print_simple_term t;
      match t' with
         Single   -> print_pass ()
       | _        -> print_fail ()

let test_floatDouble () =
   print_head "floatDouble" "Double";
   let t = term_of_float_precision Double in
   let t' = float_precision_of_term t in
      print_simple_term t;
      match t' with
         Double   -> print_pass ()
       | _        -> print_fail ()

let test_floatLongDouble () =
   print_head "floatLongDouble" "LongDouble";
   let t = term_of_float_precision LongDouble in
   let t' = float_precision_of_term t in
      print_simple_term t;
      match t' with
         LongDouble  -> print_pass ()
       | _           -> print_fail ()

(*************************************************************************
 * Define a function to run all the above tests.
 *************************************************************************)

let run_tests () =
   fail_count := 0;
   Printf.printf "\n\n==> Beginning base tests <==\n\n";
   test_int ();
   test_rawint ();
   test_rawfloat ();
   test_val_true ();
   test_val_false ();
   test_string ();
   test_int8 ();
   test_int16 ();
   test_int32 ();
   test_int64 ();
   test_int_signed_true ();
   test_int_signed_false ();
   test_floatSingle ();
   test_floatDouble ();
   test_floatLongDouble ();
   !fail_count
