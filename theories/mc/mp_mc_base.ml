(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Provides basic code for debugging and term
 * construction / deconstruction.
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

open Refiner.Refiner.Term
open Simple_print.SimplePrint

(*************************************************************************
 * Debugging.
 *************************************************************************)

(* Set this to true to enable debugging output from the functions below. *)

let debug = ref false

(* Simple functions for debug printing of strings and terms. *)

let debug_string str =
   if !debug then print_string ("\n" ^ str ^ "\n")

let debug_term term =
   if !debug then begin
      print_string "\n";
      print_simple_term term;
      print_string "\n"
   end

let print_term term =
      print_string "\n";
      print_simple_term term;
      print_string "\n"

