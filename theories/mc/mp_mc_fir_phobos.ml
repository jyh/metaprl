(*!
 * @begin[doc]
 * @theory[Mp_mc_fir_phobos]
 *
 * The @tt[Mp_mc_fir_phobos] module provides phobosC.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 2002 Adam Granicz, Caltech
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
 * Author: Adam Granicz
 * @email{granicz@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Base_theory
include Itt_theory
include Mp_mc_fir_exp
include Mp_mc_fir_phobos_exp
(*! @docoff *)

open Opname
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.RefineError
open Top_conversionals
open Simple_print.SimplePrint
open Phobos_type

(*
 * Simple debugging utilities.
 * They depend on -debug_compiler
 *)
let debug_string s =
   if !Fir_state.debug_compiler then
      print_string s

let debug_term t =
   if !Fir_state.debug_compiler then
      print_simple_term t

(*
 * Examining special terms.
 *)

(*
 * Return a conversion that applies all given iforms.
 *)
let applyAllIFormC iform_rewrites =
   let patterns =
      List.map (fun ((redex, _), (contractum, _)) ->
            debug_string "post-rewrite : ";
            debug_term redex;
            debug_string "  ->  ";
            debug_term contractum;
            debug_string "\n";
               create_iform "post_proc" false redex contractum) iform_rewrites
   in
      repeatC (higherC (applyAllC patterns))
