(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * A test program to test MC <--> MetaPRL FIR translation code.
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

include Base_theory
include Mp_mc_theory

open Simple_print.SimplePrint
open Top_conversionals
open Mp_mc_fir_eval
open Mp_mc_const_elim

(*
 * This is the outermost rewriter we want to use to rewrite the program.
 *)

let apply_rewrite = apply_rewrite (Mp_resource.theory_bookmark "Mp_mc_theory")

(*************************************************************************
 * Define tests.
 *************************************************************************)

let test1 () =
   print_string "\n\n*** Beginning test 1...\n\n";
   let t = <<
      letUnop{ tyInt; idOp; atomInt{0}; y.
      letBinop{ tyEnum{2}; eqIntOp; atomVar{'y}; atomInt{0}; flag.
      Mp_mc_fir_exp!matchExp{ 'flag;
         cons{ matchCase{ 'dummy_label;
                          int_set{ cons{ interval{0; 0}; nil } };
                          'failure };
         cons{ matchCase{ 'dummy_label;
                          int_set{ cons{ interval{1; 1}; nil } };
                          'success };
         nil }}}}} >> in
   print_simple_term t;
   print_string "\n\nApplying firExpEvalC...\n\n";
   let t = apply_rewrite firExpEvalC t in
   print_simple_term t;
   print_string "\n"

let test2 () =
   print_string "\n\n*** Beginning test 2...\n\n";
   let t = <<
      letUnop{ tyInt; idOp; atomInt{0}; y.
      letBinop{ tyEnum{2}; eqIntOp; atomVar{'y}; atomInt{2}; flag.
      Mp_mc_fir_exp!matchExp{ 'flag;
         cons{ matchCase{ 'dummy_label;
                          int_set{ cons{ interval{0; 0}; nil } };
                          'success };
         cons{ matchCase{ 'dummy_label;
                          int_set{ cons{ interval{1; 1}; nil } };
                          'failure };
         nil }}}}} >> in
   print_simple_term t;
   print_string "\n\nApplying firExpEvalC...\n\n";
   let t = apply_rewrite firExpEvalC t in
   print_simple_term t;
   print_string "\n"

let test3 () =
   print_string "\n\n*** Beginning test 3...\n\n";
   let t = << member{ 0; interval{0; 0} } >> in
   print_simple_term t;
   print_string "\n\nApplying firExpEvalC...\n\n";
   let t = apply_rewrite firExpEvalC t in
   print_simple_term t;
   print_string "\n"

let test4 () =
   print_string "\n\n*** Beginning test 4...\n\n";
   let t = << member{ 0; int_set{ cons{ interval{0; 0}; nil } } } >> in
   print_simple_term t;
   print_string "\n\nApplying firExpEvalC...\n\n";
   let t = apply_rewrite firExpEvalC t in
   print_simple_term t;
   print_string "\n"

let test5 () =
   print_string "\n\n*** Beginning test 5...\n\n";
      let t = <<
      Mp_mc_fir_exp!matchExp{ 0;
         cons{ matchCase{ 'dummy_label;
                          int_set{ cons{ interval{0; 0}; nil } };
                          'success};
         nil }} >> in
   print_simple_term t;
   print_string "\n\nApplying firExpEvalC...\n\n";
   let t = apply_rewrite firExpEvalC t in
   print_simple_term t;
   print_string "\n"

(*************************************************************************
 * Run tests.
 *************************************************************************)

let _ =
   test1 ();
   test2 ();
   test3 ();
   test4 ();
   test5 ()
