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

let fail_count = ref 0

let print_fail () =
   fail_count := !fail_count + 1;
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

(* Naml ints. *)

let test_uminusIntOp () =
   print_head "uminusIntOp" "UMinusIntOp";
   let t = term_of_unop UMinusIntOp in
   let t' = unop_of_term t in
      print_simple_term t;
      match t' with
         UMinusIntOp -> print_pass ()
       | _           -> print_fail ()

(*
 * Binary operations.
 *)

(* Naml ints. *)

let test_plusIntOp () =
   print_head "plusIntOp" "PlusIntOp";
   let t = term_of_binop PlusIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         PlusIntOp   -> print_pass ()
       | _           -> print_fail ()

let test_minusIntOp () =
   print_head "minusIntOp" "MinusIntOp";
   let t = term_of_binop MinusIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         MinusIntOp  -> print_pass ()
       | _           -> print_fail ()

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

let test_remIntOp () =
   print_head "remIntOp" "RemIntOp";
   let t = term_of_binop RemIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         RemIntOp -> print_pass ()
       | _        -> print_fail ()

let test_lslIntOp () =
   print_head "lslIntOp" "LslIntOp";
   let t = term_of_binop LslIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         LslIntOp -> print_pass ()
       | _        -> print_fail ()

let test_lsrIntOp () =
   print_head "lsrIntOp" "LsrIntOp";
   let t = term_of_binop LsrIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         LsrIntOp -> print_pass ()
       | _        -> print_fail ()

let test_asrIntOp () =
   print_head "asrIntOp" "AsrIntOp";
   let t = term_of_binop AsrIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         AsrIntOp -> print_pass ()
       | _        -> print_fail ()

let test_andIntOp () =
   print_head "andIntOp" "AndIntOp";
   let t = term_of_binop AndIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         AndIntOp -> print_pass ()
       | _        -> print_fail ()

let test_orIntOp () =
   print_head "orIntOp" "OrIntOp";
   let t = term_of_binop OrIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         OrIntOp  -> print_pass ()
       | _        -> print_fail ()

let test_xorIntOp () =
   print_head "xorIntOp" "XorIntOp";
   let t = term_of_binop XorIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         XorIntOp -> print_pass ()
       | _        -> print_fail ()

let test_maxIntOp () =
   print_head "maxIntOp" "MaxIntOp";
   let t = term_of_binop MaxIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         MaxIntOp -> print_pass ()
       | _        -> print_fail ()

let test_minIntOp () =
   print_head "minIntOp" "MinIntOp";
   let t = term_of_binop MinIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         MinIntOp -> print_pass ()
       | _        -> print_fail ()

let test_eqIntOp () =
   print_head "eqIntOp" "EqIntOp";
   let t = term_of_binop EqIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         EqIntOp  -> print_pass ()
       | _        -> print_fail ()

let test_neqIntOp () =
   print_head "neqIntOp" "NeqIntOp";
   let t = term_of_binop NeqIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         NeqIntOp -> print_pass ()
       | _        -> print_fail ()

let test_ltIntOp () =
   print_head "ltIntOp" "LtIntOp";
   let t = term_of_binop LtIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         LtIntOp  -> print_pass ()
       | _        -> print_fail ()

let test_leIntOp () =
   print_head "leIntOp" "LeIntOp";
   let t = term_of_binop LeIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         LeIntOp  -> print_pass ()
       | _        -> print_fail ()

let test_gtIntOp () =
   print_head "gtIntOp" "GtIntOp";
   let t = term_of_binop GtIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         GtIntOp  -> print_pass ()
       | _        -> print_fail ()

let test_geIntOp () =
   print_head "geIntOp" "GeIntOp";
   let t = term_of_binop GeIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         GeIntOp  -> print_pass ()
       | _        -> print_fail ()

let test_cmpIntOp () =
   print_head "cmpIntOp" "CmpIntOp";
   let t = term_of_binop CmpIntOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         CmpIntOp -> print_pass ()
       | _        -> print_fail ()

(*************************************************************************
 * Define a function to run all the above tests.
 *************************************************************************)

let run_tests () =
   fail_count := 0;
   Printf.printf "\n\n==> Beginning exp tests <==\n\n";
   test_idOp ();
   test_uminusIntOp ();
   test_plusIntOp ();
   test_minusIntOp ();
   test_mulIntOp ();
   test_divIntOp ();
   test_remIntOp ();
   test_lslIntOp ();
   test_lsrIntOp ();
   test_asrIntOp ();
   test_andIntOp ();
   test_orIntOp ();
   test_xorIntOp ();
   test_maxIntOp ();
   test_minIntOp ();
   test_eqIntOp ();
   test_neqIntOp ();
   test_ltIntOp ();
   test_leIntOp ();
   test_gtIntOp ();
   test_geIntOp ();
   test_cmpIntOp ();
   !fail_count
