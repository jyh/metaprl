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

extends Czf_wf;;
extends Czf_false;;

declare implies{'A; 'B};;
define not_abs : not{'A} <--> 'A => false;;

(*
 * Intro.
 *
 * H >> A => B
 * by implicationIntro
 * H, x: A >> B
 * H >> W wf
 *)
rule implies_intro 'x :
   sequent { 'H; x: 'A >> 'B } -->
   sequent { 'H >> wf{'A} } -->
   sequent { 'H >> 'A => 'B };;

(*
 * Elimination.
 *
 * H, x: A => B, J >> T
 * by implies_elim i
 * H, x: A => B, J >> A
 * H, x: A => B, J, y: B >> T
 *)
rule implies_elim 'H 'J 'y :
   sequent { 'H; x: 'A => 'B; 'J >> 'A } -->
   sequent { 'H; x: 'A => 'B; 'J; y: 'B >> 'T } -->
   sequent { 'H; x: 'A => 'B; 'J >> 'T };;

(*
 * Well formedness.
 *)
rule implies_wf :
   sequent { 'H >> wf{'A} } -->
   sequent { 'H >> wf{'B} } -->
   sequent { 'H >> wf{'A => 'B} };;

(*
 * Implication is restricted.
 *)
rule implies_res :
   sequent { 'H >> restricted{'A} } -->
   sequent { 'H >> restricted{'B} } -->
   sequent { 'H >> restricted{'A => 'B} };;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
