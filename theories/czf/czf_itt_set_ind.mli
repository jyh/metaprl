(*
 * Helpful rules about induction combinator.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Dependent function types.
 *)
axiom set_ind_dfun_type 'H (bind{u. 'B['u]}) :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; u: set >- "type"{'B['u]} } -->
   sequent [squash] { 'H >- fun_prop{u. 'B['u]} } -->
   sequent ['ext] { 'H >- "type"{set_ind{'s; T, f, g. x: 'T -> 'B['f 'x]}} }

axiom set_ind_dfun_fun 'H (bind{x. bind{y. 'B['x; 'y]}}) 'u 'v :
   sequent ['ext] { 'H >- fun_set{z. 'A['z]} } -->
   sequent [squash] { 'H; u: set; v: set >- "type"{'B['u; 'v]} } -->
   sequent ['ext] { 'H; u: set >- fun_prop{z. 'B['u; 'z]} } -->
   sequent ['ext] { 'H; v: set >- fun_prop{z. 'B['z; 'v]} } -->
   sequent ['ext] { 'H >- fun_prop{z. set_ind{'A['z]; T, f, g. x: 'T -> 'B['z; 'f 'x]}} }

(*
 * Dependent product types.
 *)
axiom set_ind_dprod_type 'H (bind{u. 'B['u]}) :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; u: set >- "type"{'B['u]} } -->
   sequent [squash] { 'H >- fun_prop{u. 'B['u]} } -->
   sequent ['ext] { 'H >- "type"{set_ind{'s; T, f, g. x: 'T * 'B['f 'x]}} }

axiom set_ind_dprod_fun 'H (bind{x. bind{y. 'B['x; 'y]}}) 'u 'v :
   sequent ['ext] { 'H >- fun_set{z. 'A['z]} } -->
   sequent [squash] { 'H; u: set; v: set >- "type"{'B['u; 'v]} } -->
   sequent ['ext] { 'H; u: set >- fun_prop{z. 'B['u; 'z]} } -->
   sequent ['ext] { 'H; v: set >- fun_prop{z. 'B['z; 'v]} } -->
   sequent ['ext] { 'H >- fun_prop{z. set_ind{'A['z]; T, f, g. x: 'T * 'B['z; 'f 'x]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
