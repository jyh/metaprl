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

extends Base_theory
extends Itt_rfun
extends Itt_atom
extends Mp_mc_theory
extends Mp_mc_inline
extends Mp_mc_inline_aux
extends Mp_mc_fir_phobos_exp

open Simple_print.SimplePrint
open Top_conversionals
open Mp_mc_fir_eval
open Mp_mc_deadcode
open Mp_mc_const_elim
open Mp_mc_inline
open Mp_mc_inline_aux
open Mp_mc_fir_phobos_exp

(*
 * These are the rewriters we want to use to rewrite terms.
 *)

let apply_rewrite_top =
    apply_rewrite (Mp_resource.theory_bookmark "Mp_mc_theory")

let apply_rewrite_phobos =
    apply_rewrite (Mp_resource.theory_bookmark "Mp_mc_fir_phobos_exp")

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
   let t = apply_rewrite_top firExpEvalC t in
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
   let t = apply_rewrite_top firExpEvalC t in
   print_simple_term t;
   print_string "\n"

let test3 () =
   print_string "\n\n*** Beginning test 3...\n\n";
   let t = << member{ 0; interval{0; 0} } >> in
   print_simple_term t;
   print_string "\n\nApplying firExpEvalC...\n\n";
   let t = apply_rewrite_top firExpEvalC t in
   print_simple_term t;
   print_string "\n"

let test4 () =
   print_string "\n\n*** Beginning test 4...\n\n";
   let t = << member{ 0; int_set{ cons{ interval{0; 0}; nil } } } >> in
   print_simple_term t;
   print_string "\n\nApplying firExpEvalC...\n\n";
   let t = apply_rewrite_top firExpEvalC t in
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
   let t = apply_rewrite_top firExpEvalC t in
   print_simple_term t;
   print_string "\n"

let test6 () =
   print_string "\n\n*** Beginning test 6...\n\n";
   let t = <<
      letUnop{ tyInt; idOp; atomInt{0}; y.
      setSubscript{ 'subop; 'label; 'y; 'atom1; 'ty; 'atom2; 'y }} >> in
   print_simple_term t;
   print_string "\n\nApplying firExpEvalC...\n\n";
   let t = apply_rewrite_top firExpEvalC t in
   print_simple_term t;
   print_string "\n"

let test7 () =
   print_string "\n\n*** Beginning test 7...\n\n";
   let t = <<
      letBinop{ tyInt; plusIntOp; atomInt{0}; atomInt{1}; y.
      'y }
   >> in
   print_simple_term t;
   print_string "\n\nApplying firDeadcodeC...\n\n";
   let t = apply_rewrite_top firDeadcodeC t in
   print_simple_term t;
   print_string "\nNothing should have changed...\n"

let test8 () =
   print_string "\n\n*** Beginning test 8...\n\n";
   let t = <<
      letBinop{ tyInt; plusIntOp; atomInt{0}; atomInt{1}; y.
      'nothing }
   >> in
   print_simple_term t;
   print_string "\n\nApplying firDeadcodeC...\n\n";
   let t = apply_rewrite_top firDeadcodeC t in
   print_simple_term t;
   print_string "\nWe should be down to 'nothing...\n"

let test9 () =
   print_string "\n\n*** Beginning test 9...\n\n";
   let t = << variable["blah":s] >> in
   print_simple_term t;
   print_string "\n\nApplying reduce_phobos_variable\n\n";
   let t = apply_rewrite_phobos reduce_phobos_variable t in
   print_simple_term t;
   print_string "\nWe should be down to 'blah...\n"

(*************************************************************************
 * Run tests.
 *************************************************************************)

let _ =
   test1 ();
   test2 ();
   test3 ();
   test4 ();
   test5 ();
   test6 ();
   test7 ();
   test8 ();
   test9 ()
