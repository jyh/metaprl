(*
 * Interpretation of universial quantifier.
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

extends Itt_theory
extends Fol_univ_itt
extends Fol_all

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

prim_rw unfold_all : "all"{x. 'B['x]} <--> bisect{'B[void]; 'B[unit]}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive all_type 'x :
   sequent ['ext] { 'H; x: univ >- "type"{'B[prop{'x}]} } -->
   sequent ['ext] { 'H >- "type"{."all"{y. 'B['y]}} }

interactive all_intro 'x :
   sequent ['ext] { 'H; x: univ >- 'B[prop{'x}] } -->
   sequent ['ext] { 'H; x: univ >- "type"{'B[prop{'x}]} } -->
   sequent ['ext] { 'H >- "all"{y. 'B['y]} }

interactive all_elim 'H 'x 'z 'a :
   sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x] >- "type"{'a} } -->
   sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x]; z: 'B['a] >- 'C['x] } -->
   sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x] >- 'C['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
