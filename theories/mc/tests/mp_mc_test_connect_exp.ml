(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * A test program to test MC <--> MetaPRL FIR translation code.
 * This module tests FIR expressions.
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

open Fir

(* Open MetaPRL namespaces. *)

open Mp_mc_connect_exp
open Simple_print.SimplePrint

(* Open ML namespaces. *)

open Printf

(* General functions. *)

let print_head name fir_obj =
   printf "test_%s:\n%s\n" name fir_obj

let print_pass () =
   printf "\nTest passes.\n\n"

let print_fail () =
   printf "\n===> TEST FAILS! <===\n\n"

(*************************************************************************
 * Define test functions.
 *************************************************************************)

(*
 * Unary operations.
 *)

(* Identity (polymorphic). *)

let test_idOp () =
   print_head "idOp" "IdOp";
   let t = term_of_unop IdOp in
   let t' = unop_of_term t in
      print_simple_term t;
      match t' with
         IdOp  -> print_pass ()
       | _     -> print_fail ()

(*
 * Binary operations.
 *)

(* Naml ints. *)

let test_mulIntOp () =
   print_head "mulIntOp" "MulIntOp";
   let t = term_of_binop MulIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         MulIntOp -> print_pass ()
       | _        -> print_fail ()

let test_divIntOp () =
   print_head "divIntOp" "DivIntOp";
   let t = term_of_binop DivIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         DivIntOp -> print_pass ()
       | _        -> print_fail ()

(*************************************************************************
 * Define a function to run all the above tests.
 *************************************************************************)

let run_tests () =
   test_idOp ();
   test_mulIntOp ();
   test_divIntOp ()
