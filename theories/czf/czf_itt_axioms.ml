(*
 * These are the axioms of CZF set theory.
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

include Czf_itt_true
include Czf_itt_false
include Czf_itt_and
include Czf_itt_or
include Czf_itt_implies
include Czf_itt_all
include Czf_itt_exists
include Czf_itt_sall
include Czf_itt_sexists
include Czf_itt_dall
include Czf_itt_dexists
include Czf_itt_rel

open Printf
open Mp_debug

open Tactic_type
open Var

let _ =
   show_loading "Loading CZF_itt_axioms%t"

(*
 * Set induction.
 *
 * H >- all x. P(x)
 * by set_induction
 * H; x: set; w: (all y: x. P(y)) >- P(x)
 * H >- P(x) wf
 *)
interactive set_induction 'H 'x 'w :
   sequent ['ext] { 'H; x: set >- "type"{'P['x]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'P['z]} } -->
   sequent ['ext] { 'H; x: set; w: dall{'x; z. 'P['z]} >- 'P['x] } -->
   sequent ['ext] { 'H >- sall{z. 'P['z]} }

let setInduction1 p =
   let x, w = maybe_new_vars2 p "x" "w" in
      set_induction (Sequent.hyp_count_addr p) x w p

interactive set_induction2 'H 'J 'x 'y 'w :
   sequent ['ext] { 'H; x: set; 'J['x]; y: set >- "type"{'C['y]} } -->
   sequent ['ext] { 'H; x: set; 'J['x] >- fun_prop{y. 'C['y]} } -->
   sequent ['ext] { 'H; x: set; 'J['x]; y: set; z: dall{'y; w. 'C['w]} >- 'C['y] }-->
   sequent ['ext] { 'H; x: set; 'J['x] >- 'C['x] }

let setInduction i p =
   let x, y, w = maybe_new_vars3 p "x" "y" "w" in
   let j, k = Sequent.hyp_indices p i in
      set_induction2 j k x y w p

(*
 * Restricted separation.
 *)
interactive separation 'H (bind{v. 'P['v]}) 'a 'b 'w 'x :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H; b: set >- "type"{'P['b]} } -->
   sequent ['ext] { 'H >- restricted{b. 'P['b]} } -->
   sequent ['ext] { 'H; b: set; w: sall{x. iff{member{'x; 'b}; .member{'x; 'a} & 'P['x]}} >- 'C } -->
   sequent ['ext] { 'H >- 'C }

(*
 * Strong collection.
 *)
interactive collection 'H 's1 (bind{x. bind{y. 'P['x; 'y]}}) 's2 'x 'y 'w :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H; x: set; y: set >- "type"{'P['x; 'y]} } -->
   sequent ['ext] { 'H >- dall{'s1; x. sexists{y. 'P['x; 'y]}} } -->
   sequent ['ext] { 'H; s2: set; w: rel{x, y. 'P['x; 'y]; 's1; 's2} >- 'C } -->
   sequent ['ext] { 'H >- 'C }

(*
 * Subset collection.
 *)
interactive subset_collection 'H 'a 'b 'c bind{u. bind{x. bind{y. 'P['u; 'x; 'y]}}} :
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- isset{'b} } -->
   sequent [squash] { 'H; u: set; x: set; y: set >- "type"{'P['u; 'x; 'y]} } -->
   sequent ['ext] { 'H; u: set; x: set >- fun_prop{y. 'P['u; 'x; 'y]} } -->
   sequent ['ext] { 'H; w: sexists{c. sall{u. dall{'a; x. dexists{'b; y. 'P['u; 'x; 'y]}} => dexists{'c; z. rel{x, y. 'P['u; 'x; 'y]; 'a; 'z}}}} >- 'C } -->
   sequent ['ext] { 'H >- 'C }


(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
