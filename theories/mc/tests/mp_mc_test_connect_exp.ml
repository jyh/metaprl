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

(* Open MC namespaces. *)

include Base_theory
open Rawint
open Rawfloat
open Fir

(* Open MetaPRL namespaces. *)

open Mp_mc_connect_exp
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

let unop_test unop str =
   printf "--> Test: %s\n" str;
   let t = term_of_unop unop in
   let t' = unop_of_term t in
      print_simple_term t;
      if t' = unop then
         print_pass ()
      else
         print_fail ()

let binop_test binop str =
   printf "--> Test: %s\n" str;
   let t = term_of_binop binop in
   let t' = binop_of_term t in
      print_simple_term t;
      if t' = binop then
         print_pass ()
      else
         print_fail ()

let sub_block_test sub_block str =
   printf "--> Test: %s\n" str;
   let t = term_of_sub_block sub_block in
   let t' = sub_block_of_term t in
      print_simple_term t;
      if t' = sub_block then
         print_pass ()
      else
         print_fail ()

let sub_value_test sub_value str =
   printf "--> Test: %s\n" str;
   let t = term_of_sub_value sub_value in
   let t' = sub_value_of_term t in
      print_simple_term t;
      if t' = sub_value then
         print_pass ()
      else
         print_fail ()

let sub_index_test sub_index str =
   printf "--> Test: %s\n" str;
   let t = term_of_sub_index sub_index in
   let t' = sub_index_of_term t in
      print_simple_term t;
      if t' = sub_index then
         print_pass ()
      else
         print_fail ()

let sub_script_test sub_script str =
   printf "--> Test: %s\n" str;
   let t = term_of_sub_script sub_script in
   let t' = sub_script_of_term t in
      print_simple_term t;
      if t' = sub_script then
         print_pass ()
      else
         print_fail ()

let subop_test subop str =
   printf "--> Test: %s\n" str;
   let t = term_of_subop subop in
   let t' = subop_of_term t in
      print_simple_term t;
      if t' = subop then
         print_pass ()
      else
         print_fail ()

let atom_test atom str =
   printf "--> Test: %s\n" str;
   let t = term_of_atom atom in
   let t' = atom_of_term t in
      print_simple_term t;
      if t' = atom then
         print_pass ()
      else
         print_fail ()

let alloc_op_test alloc_op str =
   printf "--> Test: %s\n" str;
   let t = term_of_alloc_op alloc_op in
   let t' = alloc_op_of_term t in
      print_simple_term t;
      if t' = alloc_op then
         print_pass ()
      else
         print_fail ()

let tailop_test tailop str =
   printf "--> Test: %s\n" str;
   let t = term_of_tailop tailop in
   let t' = tailop_of_term t in
      print_simple_term t;
      if t' = tailop then
         print_pass ()
      else
         print_fail ()

let pred_nop_test pred_nop str =
   printf "--> Test: %s\n" str;
   let t = term_of_pred_nop pred_nop in
   let t' = pred_nop_of_term t in
      print_simple_term t;
      if t' = pred_nop then
         print_pass ()
      else
         print_fail ()

let pred_unop_test pred_unop str =
   printf "--> Test: %s\n" str;
   let t = term_of_pred_unop pred_unop in
   let t' = pred_unop_of_term t in
      print_simple_term t;
      if t' = pred_unop then
         print_pass ()
      else
         print_fail ()

let pred_binop_test pred_binop str =
   printf "--> Test: %s\n" str;
   let t = term_of_pred_binop pred_binop in
   let t' = pred_binop_of_term t in
      print_simple_term t;
      if t' = pred_binop then
         print_pass ()
      else
         print_fail ()

let pred_test pred str =
   printf "--> Test: %s\n" str;
   let t = term_of_pred pred in
   let t' = pred_of_term t in
      print_simple_term t;
      if t' = pred then
         print_pass ()
      else
         print_fail ()

let debug_line_test debug_line str =
   printf "--> Test: %s\n" str;
   let t = term_of_debug_line debug_line in
   let t' = debug_line_of_term t in
      print_simple_term t;
      if t' = debug_line then
         print_pass ()
      else
         print_fail ()

let debug_vars_test debug_vars str =
   printf "--> Test: %s\n" str;
   let t = term_of_debug_vars debug_vars in
   let t' = debug_vars_of_term t in
      print_simple_term t;
      if t' = debug_vars then
         print_pass ()
      else
         print_fail ()

let debug_info_test debug_info str =
   printf "--> Test: %s\n" str;
   let t = term_of_debug_info debug_info in
   let t' = debug_info_of_term t in
      print_simple_term t;
      if t' = debug_info then
         print_pass ()
      else
         print_fail ()

let exp_test exp str =
   printf "--> Test: %s\n" str;
   let t = term_of_exp exp in
   let t' = exp_of_term t in
      print_simple_term t;
      if t' = exp then
         print_pass ()
      else
         print_fail ()

(*
 * Define a function to run all the tests.
 *)

let run_tests () =
   fail_count := 0;
   Printf.printf "\n\n==> Beginning exp tests <==\n\n";

   (* Unary operations. *)
   unop_test IdOp "IdOp";
   unop_test UMinusIntOp "UMinusIntOp";
   unop_test NotIntOp "NotIntOp";
   unop_test (RawBitFieldOp Int8 false 2 3) "RawBitFieldOp Int8 false 2 3";
   unop_test (UMinusRawIntOp Int16 true) "UMinusRawIntOp Int16 true";
   unop_test (NotRawIntOp Int64 false) "NotRawIntOp Int64 false";
   unop_test (UMinusFloatOp Single) "UMinusFloatOp Single";
   unop_test (AbsFloatOp Double) "AbsFloatOp Double";
   unop_test (SinOp LongDouble) "SinOp LongDouble";
   unop_test (CosOp Single) "CosOp Single";
   unop_test (SqrtOp Double) "SqrtOp Double";
   unop_test (IntOfFloatOp Single) "IntOfFloatOp Single";
   unop_test (FloatOfIntOp Double) "FloatOfIntOp Double";
   unop_test (FloatOfFloatOp Single Double) "FloatOfFloatOp Single Double";
   unop_test (FloatOfRawIntOp Single Int32 true)
             "FloatOfRawIntOp Single Int32 true";
   unop_test (RawIntOfIntOp Int32 false) "RawIntOfIntOp Int32 false";
   unop_test (RawIntOfEnumOp Int8 true 54) "RawIntOfEnumOp Int8 true 54";
   unop_test (RawIntOfFloatOp Int16 true Double)
             "RawIntOfFloatOp Int16 true Double";
   unop_test (RawIntOfRawIntOp Int32 true Int64 false)
             "RawIntOfRawIntOp Int32 true Int64 false";
   unop_test (RawIntOfPointerOp Int16 false) "RawIntOfPointerOp Int16 false";
   unop_test (PointerOfRawIntOp Int32 true) "PointerOfRawIntOp Int32 true";

   (* Binary operations. *)
   binop_test (AndEnumOp 3) "AndEnumOp 3";
   binop_test (OrEnumOp 4) "OrEnumOp 4";
   binop_test (XorEnumOp 5) "XorEnumOp 5";
   binop_test PlusIntOp "PlusIntOp";
   binop_test MinusIntOp "MinusIntOp";
   binop_test MulIntOp "MulIntOp";
   binop_test DivIntOp "DivIntOp";
   binop_test RemIntOp "RemIntOp";
   binop_test LslIntOp "LslIntOp";
   binop_test LsrIntOp "LsrIntOp";
   binop_test AsrIntOp "AsrIntOp";
   binop_test AndIntOp "AndIntOp";
   binop_test OrIntOp "OrIntOp";
   binop_test XorIntOp "XorIntOp";
   binop_test MaxIntOp "MaxIntOp";
   binop_test MinIntOp "MinIntOp";
   binop_test EqIntOp "EqIntOp";
   binop_test NeqIntOp "NeqIntOp";
   binop_test LtIntOp "LtIntOp";
   binop_test LeIntOp "LeIntOp";
   binop_test GtIntOp "GtIntOp";
   binop_test GeIntOp "GeIntOp";
   binop_test CmpIntOp "CmpIntOp";
   binop_test (PlusRawIntOp Int8 true) "PlusRawIntOp Int8 true";
   binop_test (MinusRawIntOp Int8 true) "MinusRawIntOp Int8 true";
   binop_test (MulRawIntOp Int8 true) "MulRawIntOp Int8 true";
   binop_test (DivRawIntOp Int8 true) "DivRawIntOp Int8 true";
   binop_test (RemRawIntOp Int8 true) "RemRawIntOp Int8 true";
   binop_test (SlRawIntOp Int8 true) "SlRawIntOp Int8 true";
   binop_test (SrRawIntOp Int8 true) "SrRawIntOp Int8 true";
   binop_test (AndRawIntOp Int8 true) "AndRawIntOp Int8 true";
   binop_test (OrRawIntOp Int8 true) "OrRawIntOp Int8 true";
   binop_test (XorRawIntOp Int8 true) "XorRawIntOp Int8 true";
   binop_test (MaxRawIntOp Int8 true) "MaxRawIntOp Int8 true";
   binop_test (MinRawIntOp Int8 true) "MinRawIntOp Int8 true";
   binop_test (RawSetBitFieldOp Int8 true 2 3)
              "RawSetBitFieldOp Int8 true 2 3";
   binop_test (EqRawIntOp Int8 true) "EqRawIntOp Int8 true";
   binop_test (NeqRawIntOp Int8 true) "NeqRawIntOp Int8 true";
   binop_test (LtRawIntOp Int8 true) "LtRawIntOp Int8 true";
   binop_test (LeRawIntOp Int8 true) "LeRawIntOp Int8 true";
   binop_test (GtRawIntOp Int8 true) "GtRawIntOp Int8 true";
   binop_test (GeRawIntOp Int8 true) "GeRawIntOp Int8 true";
   binop_test (CmpRawIntOp Int8 true) "CmpRawIntOp Int8 true";
   binop_test (PlusFloatOp Single) "PlusFloatOp Single";
   binop_test (MinusFloatOp Single) "MinusFloatOp Single";
   binop_test (MulFloatOp Single) "MulFloatOp Single";
   binop_test (DivFloatOp Single) "DivFloatOp Single";
   binop_test (RemFloatOp Single) "RemFloatOp Single";
   binop_test (MaxFloatOp Single) "MaxFloatOp Single";
   binop_test (MinFloatOp Single) "MinFloatOp Single";
   binop_test (EqFloatOp Single) "EqFloatOp Single";
   binop_test (NeqFloatOp Single) "NeqFloatOp Single";
   binop_test (LtFloatOp Single) "LtFloatOp Single";
   binop_test (LeFloatOp Single) "LeFloatOp Single";
   binop_test (GtFloatOp Single) "GtFloatOp Single";
   binop_test (GeFloatOp Single) "GeFloatOp Single";
   binop_test (CmpFloatOp Single) "CmpFloatOp Single";
   binop_test (Atan2Op Single) "Atan2Op Single";
   binop_test EqEqOp "EqEqOp";
   binop_test NeqEqOp "NeqEqOp";
   binop_test (PlusPointerOp Int8 false) "PlusPointerOp Int8 false";

   (* Subscript operators. *)
   sub_block_test BlockSub "BlockSub";
   sub_block_test RawDataSub "RawDataSub";
   sub_block_test TupleSub "TupleSub";
   sub_block_test RawTupleSub "RawTupleSub";
   sub_value_test PolySub "PolySub";
   sub_value_test (RawIntSub Int8 false) "RawIntSub Int8 false";
   sub_value_test (RawFloatSub Single) "RawFloatSub Single";
   sub_value_test PointerSub "PointerSub";
   sub_value_test FunctionSub "FunctionSub";
   sub_index_test ByteIndex "ByteIndex";
   sub_index_test WordIndex "WordIndex";
   sub_script_test IntIndex "IntIndex";
   sub_script_test (RawIntIndex Int8 true) "RawIntIndex Int8 true";
   let op = { sub_block = BlockSub;  sub_value = PolySub;
              sub_index = ByteIndex; sub_script = IntIndex } in
   subop_test op "{ BlockSub; PolySub; ByteIndex; IntIndex }";

   (* Normal values. *)
   atom_test (AtomNil TyInt) "AtomNil TyInt";
   atom_test (AtomInt 2) "AtomInt 2";
   atom_test (AtomEnum 3 2) "AtomEnum 3 2";
   atom_test (AtomRawInt (Rawint.of_string Int8 true "23"))
             "AtomRawInt (Rawint.of_string Int8 true \"23\")";
   atom_test (AtomFloat (Rawfloat.of_string Single "2.3"))
             "AtomFloat (Rawfloat.of_string Single \"2.3\")";
   atom_test (AtomConst TyInt var1 3) "AtomConst TyInt var1 3";
   atom_test (AtomVar var1) "AtomVar var1";

   (* Allocation operators. *)
   alloc_op_test (AllocTuple RawTuple TyInt [AtomInt 3])
                 "AllocTuple RawTuple TyInt [AtomInt 3]";
   alloc_op_test (AllocUnion TyInt var2 3 [])
                 "AllocUnion TyInt var2 3 []";
   alloc_op_test (AllocArray TyInt [AtomInt 2])
                 "AllocArray TyInt [AtomInt 2]";
   alloc_op_test (AllocVArray TyInt ByteIndex (AtomInt 2) (AtomInt 3))
                 "AllocVArray TyInt ByteIndex (AtomInt 2) (AtomInt 3)";
   alloc_op_test (AllocMalloc TyInt (AtomEnum 5 2))
                 "AllocMalloc TyInt (AtomEnum 5 2)";

   (* Tail calls / operations. *)
   tailop_test (TailSysMigrate 2 (AtomInt 2) (AtomInt 3) var2 [])
               "TailSysMigrate 2 (AtomInt 2) (AtomInt 3) var2 []";
   tailop_test (TailAtomic var2 (AtomInt 2) [AtomInt 3])
               "TailAtomic var2 (AtomInt 2) [AtomInt 3]";
   tailop_test (TailAtomicRollback (AtomInt 4))
               "TailAtomicRollback (AtomInt 4)";
   tailop_test (TailAtomicCommit var2 []) "TailAtomicCommit var2 []";

   (* Predicates and assertions. *)
   pred_nop_test IsMutable "IsMutable";
   pred_unop_test Reserve "Reserve";
   pred_unop_test BoundsCheckLower "BoundsCheckLower";
   pred_unop_test BoundsCheckUpper "BoundsCheckUpper";
   pred_unop_test PolyCheck "PolyCheck";
   pred_unop_test PointerCheck "PointerCheck";
   pred_unop_test FunctionCheck "FunctionCheck";
   pred_binop_test BoundsCheck "BoundsCheck";
   pred_test (PredNop var1 IsMutable) "PredNop var1 IsMutable";
   pred_test (PredUnop var2 Reserve (AtomVar var1))
             "PredUnop var2 Reserve (AtomVar var1)";
   pred_test (PredBinop var1 BoundsCheck (AtomInt 2) (AtomInt 3))
             "PredBinop var1 BoundsCheck (AtomInt 2) (AtomInt 3)";

   (* Debugging info. *)
   debug_line_test ("Help!", 3) "\"Help!\" 3";
   debug_vars_test [(var1, TyInt, var2)] "[(var1, TyInt, var2)]";
   debug_info_test (DebugString "Hi!") "DebugString \"Hi!\"";
   let line = ("Hi!", 3) in
   debug_info_test (DebugContext line [])
                   "DebugContext (\"Hi!\", 3) []";

   (* Expressions. *)
   exp_test (LetUnop var1 TyInt UMinusIntOp (AtomInt 2) (TailCall var1 []))
            "LetUnop var1 TyInt UMinusIntOp (AtomInt 2) (TailCall var1 [])";
   exp_test (LetBinop var2 TyInt PlusIntOp (AtomInt 2) (AtomInt 3) (TailCall var1 []))
            "LetBinop var2 TyInt PlusIntOp (AtomInt 2) (AtomInt 3) (TailCall var1 [])";
   exp_test (LetExt var1 TyInt "Hi!" TyInt [] (TailCall var1 []))
            "LetExt var1 TyInt \"Hi!\" TyInt [] (TailCall var1 [])";
   exp_test (TailCall var1 [AtomInt 3]) "TailCall var1 [AtomInt 3]";
   exp_test (SpecialCall (TailAtomicRollback (AtomInt 3)))
            "SpecialCall (TailAtomicRollback (AtomInt 3))";
   exp_test (Match (AtomInt 3) [IntSet set1, TailCall var1[]])
            "Match (AtomInt 3) [IntSet set1, TailCall var1[]]";
   exp_test (TypeCase (AtomInt 1) (AtomInt 2) var1 var2 (TailCall var1 []) (TailCall var1[]))
            "TypeCase (AtomInt 1) (AtomInt 2) var1 var2 (TailCall var1 []) (TailCall var1[])";
   exp_test (LetAlloc var1 (AllocMalloc TyInt (AtomInt 3)) (TailCall var2 []))
            "LetAlloc var1 (AllocMalloc TyInt (AtomInt 3)) (TailCall var2 [])";
   exp_test (LetSubscript op var1 TyInt var2 (AtomInt 2) (TailCall var3 []))
            "LetSubscript \"op\" var1 TyInt var2 (AtomInt 2) (TailCall var3 [])";
   exp_test (SetSubscript op var1 var2 (AtomInt 2) TyInt (AtomInt 3) (TailCall var3 []))
            "SetSubscript \"op\" var1 var2 (AtomInt 2) TyInt (AtomInt 3) (TailCall var3 [])";
   exp_test (SetGlobal PolySub var1 var2 TyInt (AtomInt 3) (TailCall var3 []))
            "SetGlobal PolySub var1 var2 TyInt (AtomInt 3) (TailCall var3 [])";
   exp_test (Memcpy op var1 var2 (AtomInt 3) var2 (AtomInt 4) (AtomInt 60) (TailCall var3 []))
            "Memcpy \"op\" var1 var2 (AtomInt 3) var2 (AtomInt 4) (AtomInt 60) (TailCall var3 [])";
   exp_test (Call var1 [None; Some (AtomInt 3)] (TailCall var3 []))
            "Call var1 [None; Some (AtomInt 3)] (TailCall var3 [])";
   exp_test (Assert var1 (PredNop var2 IsMutable) (TailCall var3 []))
            "Assert var1 (PredNop var2 IsMutable) (TailCall var3 [])";
   exp_test (Debug (DebugContext line []) (TailCall var3 []))
            "Debug (DebugContext \"line\" []) (TailCall var3 [])";

   (* Done. *)
   !fail_count
