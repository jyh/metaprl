(*
 * Primitive axiomatization of implication.
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

open Refiner.Refiner.TermType

open Tactic_type.Tacticals

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

rule dprod_fun3 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'A['z]} } -->
   sequent ['ext] { 'H >- dfun_prop{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- fun_prop{z. "prod"{'A['z]; w. 'B['z; 'w]}} }

rule exists_fun 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'A['z]} } -->
   sequent ['ext] { 'H >- dfun_prop{z. 'A['z]; u, v. 'B['u; 'v]} } -->
   sequent ['ext] { 'H >- fun_prop{z. "exists"{'A['z]; w. 'B['z; 'w]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
