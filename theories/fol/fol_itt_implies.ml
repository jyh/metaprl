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

extends Itt_theory
extends Fol_itt_type

derive Fol_implies

open Tactic_type.Conversionals

prim_rw unfold_implies : Fol_implies!implies{'A; 'B} <--> Itt_rfun!"fun"{'A; 'B}
prim_rw unfold_lambda : Fol_implies!lambda{x. 'b['x]} <--> Itt_rfun!"lambda"{x. 'b['x]}
prim_rw unfold_apply : Fol_implies!apply{'f; 'a} <--> Itt_rfun!apply{'f; 'a}

let fold_implies = makeFoldC << Fol_implies!"implies"{'A; 'B} >> unfold_implies
let fold_lambda = makeFoldC << Fol_implies!lambda{x. 'b['x]} >> unfold_lambda
let fold_apply = makeFoldC << Fol_implies!apply{'f; 'a} >> unfold_apply

(************************************************************************
 * COMPUTATION                                                          *
 ************************************************************************)

derived_rw beta : Fol_implies!apply{.Fol_implies!lambda{x. 'b['x]}; 'a} <--> 'b['a]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

derived implies_type 'H :
   [wf] sequent ['ext] { 'H >- "type"{'A} } -->
   [wf] sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{.Fol_implies!implies{'A; 'B}} }

derived implies_intro 'H 'x :
   [wf] sequent ['ext] { 'H >- "type"{'A} } -->
   [main] ('b['x] : sequent ['ext] { 'H; x: 'A >- 'B }) -->
   sequent ['ext] { 'H >- Fol_implies!implies{'A; 'B} }

derived implies_elim 'H 'J 'f 'b :
   [assertion] ('a : sequent ['ext] { 'H; f: Fol_implies!implies{'A; 'B}; 'J['f] >- 'A }) -->
   [main] ('t['f; 'b] : sequent ['ext] { 'H; f: Fol_implies!implies{'A; 'B}; 'J['f]; b: 'B >- 'C['f] }) -->
   sequent ['ext] { 'H; f: Fol_implies!implies{'A; 'B}; 'J['f] >- 'C['f] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
