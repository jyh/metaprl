(*
 * Define an induction principle on the programs as defined so far.
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

extends Sil_state
extends Sil_syntax
extends Sil_sos

declare sil_program{'e1; 's1}

(*
 * Is a number a sil_program?
 *)
prim number_program {| intro [] |} :
   sequent ['ext] { <H> >- sil_program{number[i:n]; 's1} } =
   it

prim add_program (number[i:n]) 's2 (number[j:n]) 's3 :
   [main] sequent [squash] { <H> >- evalsto{eval{'e1; 's1}; ."value"{number[i:n]; 's2}} } -->
   [main] sequent [squash] { <H> >- evalsto{eval{'e2; 's2}; ."value"{number[j:n]; 's3}} } -->
   sequent ['ext] { <H> >- sil_program{add{'e1; 'e2}; 's1} } =
   it

prim sub_program (number[i:n]) 's2 (number[j:n]) 's3 :
   [main] sequent [squash] { <H> >- evalsto{eval{'e1; 's1}; ."value"{number[i:n]; 's2}} } -->
   [main] sequent [squash] { <H> >- evalsto{eval{'e2; 's2}; ."value"{number[j:n]; 's3}} } -->
   sequent ['ext] { <H> >- sil_program{sub{'e1; 'e2}; 's1} } =
   it

prim if_true_program (number[i:n]) 's2 (number[j:n]) 's3 :
   [main] sequent [squash] { <H> >- evalsto{eval{'e1; 's1}; ."value"{number[i:n]; 's2}} } -->
   [main] sequent [squash] { <H> >- evalsto{eval{'e2; 's2}; ."value"{number[j:n]; 's3}} } -->
   [assertion] sequent [squash] { <H> >- meta_eq{number[i:n]; number[j:n]; ."true"; ."false"} } -->
   [main] sequent [squash] { <H> >- sil_program{'e3; 's3} } -->
   sequent ['ext] { <H> >- sil_program{."if"{'e1; 'e2; 'e3; 'e4}; 's1} } =
   it

prim if_false_program (number[i:n]) 's2 (number[j:n]) 's3 :
   [main] sequent [squash] { <H> >- evalsto{eval{'e1; 's1}; ."value"{number[i:n]; 's2}} } -->
   [main] sequent [squash] { <H> >- evalsto{eval{'e2; 's2}; ."value"{number[j:n]; 's3}} } -->
   [assertion] sequent [squash] { <H> >- meta_eq{number[i:n]; number[j:n]; ."false"; ."true"} } -->
   [main] sequent [squash] { <H> >- sil_program{'e4; 's3} } -->
   sequent ['ext] { <H> >- sil_program{."if"{'e1; 'e2; 'e3; 'e4}; 's1} } =
   it

(*
 * Is a union a sil_program?
 *)
prim inl_program :
   [main] sequent [squash] { <H> >- sil_program{'e1; 's1} } -->
   sequent ['ext] { <H> >- sil_program{inl{'e1}; 's1} } =
   it

prim inr_program :
   [main] sequent [squash] { <H> >- sil_program{'e1; 's1} } -->
   sequent ['ext] { <H> >- sil_program{inr{'e1}; 's1} } =
   it

prim decide_left_program 'v1 's2 :
   [main] sequent [squash] { <H> >- evalsto{eval{'e1; 's1}; ."value"{inl{'v1}; 's2}} } -->
   [main] sequent [squash] { <H> >- sil_program{'e2['v1]; 's2} } -->
   sequent ['ext] { <H> >- sil_program{decide{'e1; x. 'e2['x]; y. 'e3['y]}; 's1} } =
   it

prim decide_right_program 'v1 's2 :
   [main] sequent [squash] { <H> >- evalsto{eval{'e1; 's1}; ."value"{inr{'v1}; 's2}} } -->
   [main] sequent [squash] { <H> >- sil_program{'e3['v1]; 's2} } -->
   sequent ['ext] { <H> >- sil_program{decide{'e1; x. 'e2['x]; y. 'e3['y]}; 's1} } =
   it

(*
 * Is a pair a program?
 *)
prim pair_program 'v1 's2 :
   [main] sequent [squash] { <H> >- evalsto{eval{'e1; 's1}; ."value"{'v1; 's2}} } -->
   [main] sequent [squash] { <H> >- sil_program{'e2; 's2} } -->
   sequent ['ext] { <H> >- sil_program{pair{'e1; 'e2}; 's1} } =
   it

prim spread_program 'v1 'v2 's2 :
   [main] sequent [squash] { <H> >- evalsto{eval{'e1; 's1}; ."value"{pair{'v1; 'v2}; 's2}} } -->
   [main] sequent [squash] { <H> >- sil_program{'e2['v1; 'v2]; 's2} } -->
   sequent ['ext] { <H> >- sil_program{spread{'e1; x, y. 'e2['x; 'y]}; 's1} } =
   it

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
