(*
 * Extensional squashing based on the quaotient type
 * and the Booleans.
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

include Itt_void
include Itt_unit
include Itt_quotient
include Itt_set
include Itt_bool
include Itt_logic

open Tactic_type
open Tactic_type.Conversionals

open Itt_equal
open Itt_void
open Itt_unit

declare esquash_bool{'P}
declare esquash{'P}

prec prec_esquash

dform esquash_bool : except_mode[src] :: esquash_bool{'P} =
   `"esquash_bool(" slot{'P} `")"

dform esquash_df : parens :: "prec"[prec_esquash] :: except_mode[src] :: esquash{'P} =
   Nuprl_font!downarrow slot{'P}

(*
 * Definition.
 *)
prim_rw unfold_esquash_bool : esquash_bool{'P} <-->
   (quot b1, b2 : bool // (('b1 = 'b2 in bool) or 'P))

prim_rw unfold_esquash : esquash{'P} <--> (btrue = bfalse in esquash_bool{'P})

let fold_esquash_bool = makeFoldC << esquash_bool{'P} >> unfold_esquash_bool
let fold_esquash = makeFoldC << esquash{'P} >> unfold_esquash

(*
 * Rules for esquash_bool.
 *)
interactive esquash_bool_type {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'P} } -->
   sequent ['ext] { 'H >- "type"{esquash_bool{'P}} }

interactive esquash_bool_univ {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'P IN univ[i:l] } -->
   sequent ['ext] { 'H >- esquash_bool{'P} IN univ[i:l] }

interactive esquash_bool_true {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'P} } -->
   sequent ['ext] { 'H >- btrue IN esquash_bool{'P} }

interactive esquash_bool_false {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'P} } -->
   sequent ['ext] { 'H >- bfalse IN esquash_bool{'P} }

(*
 * Typehood.
 *)
interactive esquash_type {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'P} } -->
   sequent ['ext] { 'H >- "type"{esquash{'P}} }

interactive esquash_univ {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'P IN univ[i:l] } -->
   sequent ['ext] { 'H >- esquash{'P} IN univ[i:l] }

(*
 * Introduction is not safe enough to add to the
 * intro_resource.
 *)
interactive esquash_intro 'H :
   [main] sequent [squash] { 'H >- 'P } -->
   sequent ['ext] { 'H >- esquash{'P} }

let esquashT p =
   esquash_intro (Sequent.hyp_count_addr p) p

(*
 * Elimination requires a squash conclusion.
 *)
interactive esquash_equal_elim 'H 'J :
   [main] sequent [squash] { 'H; x: 'P1; 'J[it] >- 't1[it] = 't2[it] in 'T3[it] } -->
   sequent ['ext] { 'H; x: esquash{'P1}; 'J['x] >- 't1['x] = 't2['x] in 'T3['x] }

interactive esquash_void_elim 'H 'J :
   [main] sequent [squash] { 'H; x: 'P1; 'J[it] >- void } -->
   sequent ['ext] { 'H; x: esquash{'P1}; 'J['x] >- void }

interactive esquash_esquash_elim 'H 'J :
   [main] sequent [squash] { 'H; x: 'P1; 'J[it] >- esquash{'P2[it]} } -->
   sequent ['ext] { 'H; x: esquash{'P1}; 'J['x] >- esquash{'P2['x]} }

let d_esquash_elim i p =
   let goal = Sequent.concl p in
   let j, k = Sequent.hyp_indices p i in
      if is_equal_term goal then
         esquash_equal_elim j k p
      else if is_void_term goal then
         esquash_void_elim j k p
      else
         esquash_esquash_elim j k p

let elim_resource = Mp_resource.improve elim_resource (<< esquash{'P} >>, d_esquash_elim)

interactive esquash_equal_elim2 {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; x: ('t1 = 't2 in 'T3); 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: esquash{.'t1 = 't2 in 'T3}; 'J['x] >- 'C['x] }

interactive esquash_void_elim2 {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; x: esquash{void}; 'J['x] >- 'C['x] }

interactive esquash_unit_elim2 {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: esquash{unit}; 'J['x] >- 'C['x] }

interactive esquash_esquash_elim2 {| elim_resource [] |} 'H 'J :
   sequent ['ext] { 'H; x: esquash{'P}; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: esquash{esquash{'P}}; 'J['x] >- 'C['x] }

(*
 * Equality is extensional.
 *)
interactive esquash_equal_intro {| intro_resource [] |} 'H 'x :
   [wf] sequent [squash] { 'H >- 'P1 IN univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'P2 IN univ[i:l] } -->
   [main] sequent [squash] { 'H; x: 'P1 >- 'P2 } -->
   [main] sequent [squash] { 'H; x: 'P2 >- 'P1 } -->
   sequent ['ext] { 'H >- esquash{'P1} = esquash{'P2} in univ[i:l] }

(*
 * Override the old form of set elim to use esquash instead of hide.
 *)
interactive set_elim {| elim_resource [] |} 'H 'J :
   [main] sequent ['ext] { 'H; x: 'T; z: esquash{'P['x]}; 'J['x] >- 'C['x] } -->
   sequent ['ext] { 'H; x: { y: 'T | 'P['y] }; 'J['x] >- 'C['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
