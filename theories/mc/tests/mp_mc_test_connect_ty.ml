(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * A test program to test MC <--> MetaPRL FIR translation code.
 * This module tests the FIR types.
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

(* Open MC namespaces. *)

include Base_theory
open Rawint
open Rawfloat
open Fir

(* Open MetaPRL namespaces. *)

open Mp_mc_connect_ty
open Mp_mc_test_connect_base
open Simple_print.SimplePrint

(* Open ML namespaces. *)

open Printf

(*
 * General functions and variables.
 *)

let fail_count = ref 0

let print_pass () =
   printf "\nTest passes.\n\n"

let print_fail () =
   fail_count := !fail_count + 1;
   printf "\n===> TEST FAILS! <===\n\n"

let ty_test ty str =
   printf "--> Test: %s\n" str;
   let t = term_of_ty ty in
   let t' = ty_of_term t in
      print_simple_term t;
      if t' = ty then
         print_pass ()
      else
         print_fail ()

let tydef_test tydef str =
   printf "--> Test: %s\n" str;
   let t = term_of_tydef tydef in
   let t' = tydef_of_term t in
      print_simple_term t;
      if t' = tydef then
         print_pass ()
      else
         print_fail ()

(*
 * Define a function to run all the tests.
 *)

let run_tests () =
   fail_count := 0;
   Printf.printf "\n\n==> Beginning ty / tydef tests <==\n\n";

   (* Base types. *)
   ty_test TyInt "TyInt";
   ty_test (TyEnum 3) "TyEnum 3";

   (* Native types. *)
   ty_test (TyRawInt Int8 true) "TyRawInt Int8 true";
   ty_test (TyFloat LongDouble) "TyFloat LongDouble";

   (* Functions. *)
   ty_test (TyFun [TyInt;TyEnum 2] (TyFloat Single))
           "TyFun [TyInt;TyEnum 2] (TyFloat Single)";

   (* Tuples. *)
   ty_test (TyUnion var1 [] set1) "TyUnion var1 [] set1";
   ty_test (TyTuple NormalTuple [TyInt]) "TyTuple NormalTuple [TyInt]";
   ty_test (TyArray (TyEnum 2)) "TyArray (TyEnum 2)";
   ty_test TyRawData "TyRawData";
   ty_test (TyPointer BlockSub) "TyPointer BlockSub";
   ty_test (TyFrame var1) "TyFrame var1";

   (* Polymorphism. *)
   ty_test (TyVar var2) "TyVar var2";
   ty_test (TyApply var1 [TyInt;TyEnum 2]) "TyApply var1 [TyInt;TyEnum 2]";
   ty_test (TyExists [var1;var2] TyInt) "TyExists [var1;var2] TyInt";
   ty_test (TyAll [var1;var2] TyInt) "TyAll [var1;var2] TyInt";
   ty_test (TyProject var2 2) "TyProject var2 2";

   (* Object-oriented. *)
   ty_test (TyCase TyInt) "TyCase TyInt";
   ty_test (TyObject var1 TyInt) "TyObject var1 yInt";

   (* Delayed type. *)
   ty_test TyDelayed "TyDelayed";

   (* Defining types. *)
   tydef_test (TyDefUnion [var1;var2] NormalUnion [[(TyInt,true)]])
              "TyDefUnion [var1;var2] NormalUnion [[(TyInt,true)]]";
   tydef_test (TyDefLambda [] TyInt) "TyDefLambda [] TyInt";


   (* Done. *)
   !fail_count
