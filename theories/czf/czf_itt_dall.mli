(*
 * Primitiva axiomatization of implication.
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

include Czf_itt_all
include Czf_itt_set_ind

open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "dall"{'T; x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_dall : "dall"{'s; x. 'A['x]} <-->
   set_ind{'s; a, f, g. (x: 'a -> 'A['f 'x])}

rewrite reduce_dall : "dall"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T -> 'A['f['t]])

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
rule dall_type 'H 'y :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."dall"{'s; x. 'A['x]}} }

(*
 * Intro.
 *)
rule dall_intro 'H 'a 'b :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; a: set >- "type"{'A['a]} } -->
   sequent ['ext] { 'H; a: set; b: member{'a; 's} >- 'A['a] } -->
   sequent ['ext] { 'H >- "dall"{'s; x. 'A['x]} }

(*
 * Elimination.
 *)
rule dall_elim 'H 'J 'z 'w :
   sequent [squash] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x]; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x] >- fun_prop{w. 'A['w]} } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x] >- member{'z; 's} } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x]; w: 'A['z] >- 'C['x] } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x] >- 'C['x] }

(*
 * This is a restricted formula.
 *)
rule dall_res2 'H 'w 'x :
   sequent ['ext] { 'H; w: set; x: set >- "type"{'B['w; 'x]} } -->
   sequent ['ext] { 'H >- fun_set{w. 'A['w]} } -->
   sequent ['ext] { 'H >- restricted{z, y. 'B['z; 'y]} } -->
   sequent ['ext] { 'H >- restricted{z. "dall"{'A['z]; y. 'B['z; 'y]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
