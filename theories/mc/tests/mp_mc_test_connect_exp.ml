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

open Rawint
open Rawfloat
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

(* Native ints. *)

let test_plusRawIntOp () =
   print_head "plusRawIntOp" "PlusRawIntOp Int32 true";
   let t = term_of_binop (PlusRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         PlusRawIntOp (Int32, true) -> print_pass ()
       | _                          -> print_fail ()

let test_minusRawIntOp () =
   print_head "MinusRawIntOp" "MinusRawIntOp Int32 true";
   let t = term_of_binop (MinusRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         MinusRawIntOp (Int32, true)   -> print_pass ()
       | _                             -> print_fail ()

let test_mulRawIntOp () =
   print_head "mulRawIntOp" "MulRawIntOp Int32 true";
   let t = term_of_binop (MulRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         MulRawIntOp (Int32, true)   -> print_pass ()
       | _                           -> print_fail ()

let test_divRawIntOp () =
   print_head "divRawIntOp" "DivRawIntOp Int32 true";
   let t = term_of_binop (DivRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         DivRawIntOp (Int32, true)   -> print_pass ()
       | _                           -> print_fail ()

let test_remRawIntOp () =
   print_head "remRawIntOp" "RemRawIntOp Int32 true";
   let t = term_of_binop (RemRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         RemRawIntOp (Int32, true)   -> print_pass ()
       | _                           -> print_fail ()

let test_slRawIntOp () =
   print_head "slRawIntOp" "SlRawIntOp Int32 true";
   let t = term_of_binop (SlRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         SlRawIntOp (Int32, true)   -> print_pass ()
       | _                          -> print_fail ()

let test_srRawIntOp () =
   print_head "srRawIntOp" "SrRawIntOp Int32 true";
   let t = term_of_binop (SrRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         SrRawIntOp (Int32, true)   -> print_pass ()
       | _                          -> print_fail ()

let test_andRawIntOp () =
   print_head "andRawIntOp" "AndRawIntOp Int32 true";
   let t = term_of_binop (AndRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         AndRawIntOp (Int32, true)   -> print_pass ()
       | _                           -> print_fail ()

let test_orRawIntOp () =
   print_head "orRawIntOp" "OrRawIntOp Int32 true";
   let t = term_of_binop (OrRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         OrRawIntOp (Int32, true)   -> print_pass ()
       | _                          -> print_fail ()

let test_xorRawIntOp () =
   print_head "xorRawIntOp" "XorRawIntOp Int32 true";
   let t = term_of_binop (XorRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         XorRawIntOp (Int32, true)   -> print_pass ()
       | _                           -> print_fail ()

let test_maxRawIntOp () =
   print_head "maxRawIntOp" "MaxRawIntOp Int32 true";
   let t = term_of_binop (MaxRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         MaxRawIntOp (Int32, true)   -> print_pass ()
       | _                           -> print_fail ()

let test_minRawIntOp () =
   print_head "minRawIntOp" "MinRawIntOp Int32 true";
   let t = term_of_binop (MinRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         MinRawIntOp (Int32, true)   -> print_pass ()
       | _                           -> print_fail ()

let test_rawSetBitFieldOp () =
   print_head "rawSetBitFieldOp" "RawSetBitFieldOp Int64 false 2 -56";
   let t = term_of_binop (RawSetBitFieldOp Int64 false 2 (-56)) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         RawSetBitFieldOp (Int64, false, 2, -56) -> print_pass ()
       | _                                         -> print_fail ()

let test_eqRawIntOp () =
   print_head "eqRawIntOp" "EqRawIntOp Int32 true";
   let t = term_of_binop (EqRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         EqRawIntOp (Int32, true)   -> print_pass ()
       | _                          -> print_fail ()

let test_neqRawIntOp () =
   print_head "neqRawIntOp" "NeqRawIntOp Int32 true";
   let t = term_of_binop (NeqRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         NeqRawIntOp (Int32, true)   -> print_pass ()
       | _                           -> print_fail ()

let test_ltRawIntOp () =
   print_head "ltRawIntOp" "LtRawIntOp Int32 true";
   let t = term_of_binop (LtRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         LtRawIntOp (Int32, true)   -> print_pass ()
       | _                          -> print_fail ()

let test_leRawIntOp () =
   print_head "leRawIntOp" "LeRawIntOp Int32 true";
   let t = term_of_binop (LeRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         LeRawIntOp (Int32, true)   -> print_pass ()
       | _                          -> print_fail ()

let test_gtRawIntOp () =
   print_head "gtRawIntOp" "GtRawIntOp Int32 true";
   let t = term_of_binop (GtRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         GtRawIntOp (Int32, true)   -> print_pass ()
       | _                          -> print_fail ()

let test_geRawIntOp () =
   print_head "geRawIntOp" "GeRawIntOp Int32 true";
   let t = term_of_binop (GeRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         GeRawIntOp (Int32, true)   -> print_pass ()
       | _                          -> print_fail ()

let test_cmpRawIntOp () =
   print_head "cmpRawIntOp" "CmpRawIntOp Int32 true";
   let t = term_of_binop (CmpRawIntOp Int32 true) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         CmpRawIntOp (Int32, true)   -> print_pass ()
       | _                           -> print_fail ()

(* Floats. *)

let test_plusFloatOp () =
   print_head "plusFloatOp" "PlusFloatOp Double";
   let t = term_of_binop (PlusFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         PlusFloatOp Double   -> print_pass ()
       | _                    -> print_fail ()

let test_minusFloatOp () =
   print_head "minusFloatOp" "MinusFloatOp Double";
   let t = term_of_binop (MinusFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         MinusFloatOp Double   -> print_pass ()
       | _                     -> print_fail ()

let test_mulFloatOp () =
   print_head "mulFloatOp" "MulFloatOp Double";
   let t = term_of_binop (MulFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         MulFloatOp Double   -> print_pass ()
       | _                   -> print_fail ()

let test_divFloatOp () =
   print_head "divFloatOp" "DivFloatOp Double";
   let t = term_of_binop (DivFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         DivFloatOp Double   -> print_pass ()
       | _                   -> print_fail ()

let test_remFloatOp () =
   print_head "remFloatOp" "RemFloatOp Double";
   let t = term_of_binop (RemFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         RemFloatOp Double   -> print_pass ()
       | _                   -> print_fail ()

let test_maxFloatOp () =
   print_head "maxFloatOp" "MaxFloatOp Double";
   let t = term_of_binop (MaxFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         MaxFloatOp Double   -> print_pass ()
       | _                   -> print_fail ()

let test_minFloatOp () =
   print_head "minFloatOp" "MinFloatOp Double";
   let t = term_of_binop (MinFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         MinFloatOp Double   -> print_pass ()
       | _                   -> print_fail ()

let test_eqFloatOp () =
   print_head "eqFloatOp" "EqFloatOp Double";
   let t = term_of_binop (EqFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         EqFloatOp Double   -> print_pass ()
       | _                  -> print_fail ()

let test_neqFloatOp () =
   print_head "neqFloatOp" "NeqFloatOp Double";
   let t = term_of_binop (NeqFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         NeqFloatOp Double   -> print_pass ()
       | _                   -> print_fail ()

let test_ltFloatOp () =
   print_head "ltFloatOp" "LtFloatOp Double";
   let t = term_of_binop (LtFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         LtFloatOp Double   -> print_pass ()
       | _                  -> print_fail ()

let test_leFloatOp () =
   print_head "leFloatOp" "LeFloatOp Double";
   let t = term_of_binop (LeFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         LeFloatOp Double   -> print_pass ()
       | _                  -> print_fail ()

let test_gtFloatOp () =
   print_head "gtFloatOp" "GtFloatOp Double";
   let t = term_of_binop (GtFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         GtFloatOp Double   -> print_pass ()
       | _                  -> print_fail ()

let test_geFloatOp () =
   print_head "geFloatOp" "GeFloatOp Double";
   let t = term_of_binop (GeFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         GeFloatOp Double   -> print_pass ()
       | _                  -> print_fail ()

let test_cmpFloatOp () =
   print_head "cmpFloatOp" "CmpFloatOp Double";
   let t = term_of_binop (CmpFloatOp Double) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         CmpFloatOp Double   -> print_pass ()
       | _                   -> print_fail ()

let test_atan2Op () =
   print_head "atan2Op" "Atan2Op Single";
   let t = term_of_binop (Atan2Op Single) in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         Atan2Op Single -> print_pass ()
       | _              -> print_fail ()

(* Pointer equality. *)

let test_eqEqOp () =
   print_head "eqEqOp" "EqEqOp";
   let t = term_of_binop EqEqOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         EqEqOp   -> print_pass ()
       | _        -> print_fail ()

let test_neqEqOp () =
   print_head "neqEqOp" "NeqEqOp";
   let t = term_of_binop NeqEqOp in
   let t' = binop_of_term t in
      print_simple_term t;
      match t' with
         NeqEqOp   -> print_pass ()
       | _        -> print_fail ()

(*
 * Subscript operations.
 *)

(*
 * Normal values.
 *)

(*
 * Allocation operators.
 *)

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
   test_plusRawIntOp ();
   test_minusRawIntOp ();
   test_mulRawIntOp ();
   test_divRawIntOp ();
   test_remRawIntOp ();
   test_slRawIntOp ();
   test_srRawIntOp ();
   test_andRawIntOp ();
   test_orRawIntOp ();
   test_xorRawIntOp ();
   test_maxRawIntOp ();
   test_minRawIntOp ();
   test_rawSetBitFieldOp ();
   test_eqRawIntOp ();
   test_neqRawIntOp ();
   test_ltRawIntOp ();
   test_leRawIntOp ();
   test_gtRawIntOp ();
   test_geRawIntOp ();
   test_cmpRawIntOp ();
   test_plusFloatOp ();
   test_minusFloatOp ();
   test_mulFloatOp ();
   test_divFloatOp ();
   test_remFloatOp ();
   test_maxFloatOp ();
   test_minFloatOp ();
   test_eqFloatOp ();
   test_neqFloatOp ();
   test_ltFloatOp ();
   test_leFloatOp ();
   test_gtFloatOp ();
   test_geFloatOp ();
   test_cmpFloatOp ();
   test_atan2Op ();
   test_eqEqOp ();
   test_neqEqOp ();
   !fail_count
