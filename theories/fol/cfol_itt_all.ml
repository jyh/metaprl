(*
 * Derived universal quantifier.
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
 * Copyright (C) 1999 Jason Hickey, Cornell University
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
extends Cfol_itt_base
extends Cfol_itt_and

derive Fol_all

(* Definitions *)
prim_rw unfold_all : "all"{x. 'b['x]} <--> ('b["true"] & 'b["false"])

(* Lemmas *)

(* Derived rules *)
derived all_type 'H 'x :
   [wf] sequent ['ext] { 'H; x: pred >- "type"{'B['x]} } -->
   sequent ['ext] { 'H >- "type"{."all"{y. 'B['y]}} }

derived all_intro 'H 'x :
   [main] ('b['x] : sequent ['ext] { 'H; x: pred >- 'B['x] }) -->
   [wf] sequent ['ext] { 'H; x: pred >- "type"{'B['x]} } -->
   sequent ['ext] { 'H >- "all"{y. 'B['y]} }

derived all_elim 'H 'J 'x 'z 'a :
   [wf] sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x] >- "type"{'a} } -->
   [wf] sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x]; z: pred >- "type"{'B['z]} } -->
   [main] ('b['x; 'z] : sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x]; z: 'B['a] >- 'C['x] }) -->
   sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x] >- 'C['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
