(*
 * Derive the constant true.
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

include Itt_theory
include Fol_itt_type

derive Fol_and

open Tactic_type.Conversionals

prim_rw unfold_and : "and"{'A; 'B} <--> prod{'A; 'B}
prim_rw unfold_pair : Fol_and!pair{'a; 'b} <--> Itt_dprod!pair{'a; 'b}
prim_rw unfold_spread : Fol_and!spread{'a; x, y. 'b['x; 'y]} <--> Itt_dprod!spread{'a; x, y. 'b['x; 'y]}

let fold_and = makeFoldC << Fol_and!"and"{'A; 'B} >> unfold_and
let fold_pair = makeFoldC << Fol_and!"pair"{'a; 'b} >> unfold_pair
let fold_spread = makeFoldC << Fol_and!spread{'a; x, y. 'b['x; 'y]} >> unfold_spread

(************************************************************************
 * COMPUTATION                                                          *
 ************************************************************************)

derived_rw reduce_spread : spread{pair{'x; 'y}; a, b. 'body['a; 'b]} <--> 'body['x; 'y]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

derived and_type 'H :
   [wf] sequent ['ext] { 'H >- "type"{'A} } -->
   [wf] sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{.Fol_and!"and"{'A; 'B}} }

derived and_intro 'H :
   [main] ('a : sequent ['ext] { 'H >- 'A }) -->
   [main] ('b : sequent ['ext] { 'H >- 'B }) -->
   sequent ['ext] { 'H >- Fol_and!"and"{'A; 'B} }

derived and_elim 'H 'J 'x 'y 'z :
   [main] ('body['y; 'z] : sequent ['ext] { 'H; y: 'A; z: 'B; 'J[Fol_and!pair{'y; 'z}] >- 'C[Fol_and!pair{'y; 'z}] }) -->
   sequent ['ext] { 'H; x: Fol_and!"and"{'A; 'B}; 'J['x] >- 'C['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
