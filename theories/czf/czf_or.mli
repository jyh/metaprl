(*
 * Primitiva axiomatization of implication.
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

include Czf_wf;;

declare or{'A; 'B};;
declare inl{'A};;
declare inr{'A};;

(*
 * Intro.
 *
 * H >> A \/ B
 * by or_intro_left
 * H >> A
 * H >> B wf
 *)
axiom or_intro_left 'x :
   sequent { 'H >> 'A } -->
   sequent { 'H >> wf{'B} } -->
   sequent { 'H >> 'A \/ 'B };;

axiom or_intro_right 'x :
   sequent { 'H >> 'B } -->
   sequent { 'H >> wf{'A} } -->
   sequent { 'H >> 'A \/ 'B };;

(*
 * Elimination.
 *
 * H, x: A \/ B, J[x] >> T[x]
 * by or_elim i
 * H, x: A \/ B, y: A; J[inl y] >> T[inl y]
 * H, x: A \/ B, y: B; J[inr y] >> T[inr y]
 *)
axiom or_elim 'H 'J 'y :
   sequent { 'H; x: 'A \/ 'B; y: 'A; 'J[inl{'y}] >> 'T[inl{'y}] } -->
   sequent { 'H; x: 'A \/ 'B; y: 'B; 'J[inr{'y}] >> 'T[inr{'y}] } -->
   sequent { 'H; x: 'A \/ 'B; 'J['x] >> 'T['x] };;

(*
 * Well formedness.
 *)
axiom or_wf :
   sequent { 'H >> wf{'A} } -->
   sequent { 'H >> wf{'B} } -->
   sequent { 'H >> wf{'A \/ 'B} };;

(*
 * Implication is restricted.
 *)
axiom or_res :
   sequent { 'H >> restricted{'A} } -->
   sequent { 'H >> restricted{'B} } -->
   sequent { 'H >> restricted{'A \/ 'B} };;
