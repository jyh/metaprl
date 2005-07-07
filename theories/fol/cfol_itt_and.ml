(*
 * Derived classical conjunction.
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

open Basic_tactics

derive Fol_and

(* Definitions *)
prim_rw unfold_and : "and"{'A; 'B} <--> esquash{prod{'A; 'B}}
prim_rw unfold_pair : "pair"{'a; 'b} <--> Base_trivial!it

(* Lemmas *)
interactive and_univ {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- "and"{'A; 'B} IN univ[1:l] }

(* Derived rules *)
derived and_type :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- "type"{.'A & 'B} }

derived and_intro :
   [main] sequent { <H> >- 'A } -->
   [main] sequent { <H> >- 'B } -->
   sequent { <H> >- 'A & 'B }

derived and_elim 'H :
   [wf] sequent { <H>; x: 'A & 'B; <J['x]> >- "type"{'A} } -->
   [wf] sequent { <H>; x: 'A & 'B; <J['x]> >- "type"{'B} } -->
   [main] sequent { <H>; y: 'A; z: 'B; <J['y, 'z]> >- 'C['y, 'z] } -->
   sequent { <H>; x: 'A & 'B; <J['x]> >- 'C['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
