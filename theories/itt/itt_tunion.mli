(*
 * A normal set-style union of types.
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

extends Itt_equal
extends Itt_set

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare tunion{'A; x. 'B['x]}

prec prec_tunion

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Proof of Ui
 *)
rule tunionFormation 'A :
   sequent { <H> >- 'A = 'A in univ[i:l] } -->
   sequent { <H>; x: 'A >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] }

(*
 * Typehood.
 *)
rule tunionEquality :
   sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   sequent { <H>; x: 'A1 >- 'B1['x] = 'B2['x] in univ[i:l] } -->
   sequent { <H> >- tunion{'A1; x1. 'B1['x1]} = tunion{'A2; x2. 'B2['x2] } in univ[i:l] }

rule tunionType :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- "type"{tunion{'A; x. 'B['x]}} }

(*
 * Membership.
 *)
rule tunionMemberEquality 'a :
   sequent { <H> >- 'a = 'a in 'A } -->
   sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- 'x1 = 'x2 in 'B['a] } -->
   sequent { <H> >- 'x1 = 'x2 in Union x:'A. 'B['x]  }

rule tunionMemberFormation 'a :
   sequent { <H> >- 'a = 'a in 'A } -->
   sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- 'B['a] } -->
   sequent { <H> >- Union x:'A. 'B['x]  }

(*
 * Elimination.
 *)
rule tunionElimination 'H :
   sequent { <H>; x: tunion{'A; y. 'B['y]}; <J['x]>; w: 'A; z: 'B['w] >- 't1['z] = 't2['z] in 'C['z] } -->
   sequent { <H>; x: tunion{'A; y. 'B['y]}; <J['x]> >- 't1['x] = 't2['x] in 'C['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
