(*
 * Primitiva interactiveatization of implication.
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
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

include Czf_itt_sep

open Printf
open Mp_debug

open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent
open Var

open Itt_logic
open Itt_rfun

let _ =
   show_loading "Loading Czf_itt_or%t"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Implication is restricted.
 *)
interactive union_fun {| intro_resource [] |} 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "union"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive union_res1 {| intro_resource [] |} 'H :
   ["wf"] sequent ['ext] { 'H >- "type"{'A} } -->
   ["wf"] sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- restricted{. 'A} } -->
   sequent ['ext] { 'H >- restricted{. 'B} } -->
   sequent ['ext] { 'H >- restricted{. "union"{'A; 'B}} }

(*
 * Implication is restricted.
 *)
interactive or_fun {| intro_resource [] |} 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "or"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive or_res1 {| intro_resource [] |} 'H 'w :
   ["wf"] sequent [squash] { 'H >- "type"{'A} } -->
   ["wf"] sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- restricted{. 'A} } -->
   sequent ['ext] { 'H >- restricted{. 'B} } -->
   sequent ['ext] { 'H >- restricted{. "or"{'A; 'B}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
