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
open Mp_mc_const_elim

(*
 * This is the outermost rewriter we want to use to rewrite the program.
 *)

let apply_rewrite = apply_rewrite (Mp_resource.theory_bookmark "Mp_mc_theory")

(*************************************************************************
 * Define tests.
 *************************************************************************)

let test1 () =
   print_string "\n\nBeginning test 1...\n\n";
   let t = << letBinop{ tyInt; plusIntOp; atomInt{1}; atomInt{2};
              v. 'v } >> in
   print_simple_term t;
   print_string "\nApplying firConstElimC...\n";
   let t = apply_rewrite firConstElimC t in
   print_simple_term t;
   print_string "\n"

let test2 () =
   print_string "\n\nBeginning test 2...\n\n";
   let t = << letBinop{ tyInt; plusIntOp; atomInt{1}; atomInt{2};
              v. 'v } >> in
   print_simple_term t;
   print_string "\nApplying const_elim_plusIntOp...\n";
   let t = apply_rewrite const_elim_plusIntOp t in
   print_simple_term t;
   print_string "\n"


(*************************************************************************
 * Run tests.
 *************************************************************************)

let _ =
   test1 ();
   test2 ()
