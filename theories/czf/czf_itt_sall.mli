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

extends Czf_itt_set

open Tactic_type.Tacticals
open Tactic_type.Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "sall"{x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_sall : "sall"{x. 'A['x]} <--> (all x: set. 'A['x])

topval fold_sall : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
rule sall_type 'y :
   sequent ['ext] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."sall"{x. 'A['x]} } }

(*
 * Intro.
 *)
rule sall_intro 'a :
   sequent ['ext] { 'H; a: set >- 'A['a] } -->
   sequent ['ext] { 'H >- "sall"{x. 'A['x]} }

(*
 * Elimination.
 *)
rule sall_elim 'H 'x 'z 'w :
   sequent [squash] { 'H; x: "sall"{y. 'A['y]}; 'J['x] >- isset{'z} } -->
   sequent ['ext] { 'H; x: "sall"{y. 'A['y]}; 'J['x]; w: 'A['z] >- 'T['x] } -->
   sequent ['ext] { 'H; x: "sall"{y. 'A['y]}; 'J['x] >- 'T['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
