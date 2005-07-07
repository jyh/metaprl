(*
 * Derive the constant true.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
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

derive Fol_and

open Basic_tactics

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

derived and_type :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- "type"{.Fol_and!"and"{'A; 'B}} }

derived and_intro :
   [main] ('a : sequent { <H> >- 'A }) -->
   [main] ('b : sequent { <H> >- 'B }) -->
   sequent { <H> >- Fol_and!"and"{'A; 'B} }

derived and_elim 'H :
   [main] ('body['y; 'z] : sequent { <H>; y: 'A; z: 'B; <J[Fol_and!pair{'y; 'z}]> >- 'C[Fol_and!pair{'y; 'z}] }) -->
   sequent { <H>; x: Fol_and!"and"{'A; 'B}; <J['x]> >- 'C['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
