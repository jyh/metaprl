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

open Refiner.Refiner.RefineError
open Simple_print.SimplePrint

let _ =
   try
      let base_count = Mp_mc_test_connect_base.run_tests () in
      let ty_count = Mp_mc_test_connect_ty.run_tests () in
      let exp_count = Mp_mc_test_connect_exp.run_tests () in
         Printf.printf "==> Summary <==\n\n";
         Printf.printf "Number of base cases failed: %d\n" base_count;
         Printf.printf "Number of ty cases failed: %d\n" ty_count;
         Printf.printf "Number of exp cases failed: %d\n" exp_count
   with
      (RefineError (str, StringTermError (str2, term))) ->
         Printf.eprintf "\n\nException in: %s\n" str;
         Printf.eprintf "Message: %s\n" str2;
         print_simple_term term;
         Printf.eprintf "Exiting now...\n";
