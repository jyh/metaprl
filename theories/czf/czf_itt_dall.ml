(*
 * Primitiva interactiveatization of implication.
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

include Czf_itt_all
include Czf_itt_set_ind

open Mp_debug
open Printf

open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent
open Var

open Itt_logic
open Itt_rfun

let _ =
   show_loading "Loading Czf_itt_dall%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "dall"{'T; x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_dall : "dall"{'s; x. 'A['x]} <-->
   set_ind{'s; a, f, g. (x: 'a -> 'A['f 'x])}

interactive_rw reduce_dall : "dall"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T -> 'A['f['t]])

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform dall_df : mode[prl] :: parens :: "prec"[prec_lambda] :: "dall"{'s; x. 'A} =
   pushm[0] forall slot{'x} " " Nuprl_font!member " " slot{'s} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive dall_type {| intro_resource [] |} 'H 'y :
   ["wf"] sequent [squash] { 'H >- isset{'s} } -->
   ["wf"] sequent [squash] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."dall"{'s; x. 'A['x]}} }

(*
 * Intro.
 *)
interactive dall_intro {| intro_resource [] |} 'H 'a 'b :
   ["wf"]   sequent [squash] { 'H >- isset{'s} } -->
   ["wf"]   sequent [squash] { 'H; a: set >- "type"{'A['a]} } -->
   ["main"] sequent ['ext] { 'H; a: set; b: member{'a; 's} >- 'A['a] } -->
   sequent ['ext] { 'H >- "dall"{'s; x. 'A['x]} }

(*
 * Elimination.
 *)
interactive dall_elim {| elim_resource [] |} 'H 'J 'z 'w :
   ["wf"]   sequent [squash] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x]; w: set >- "type"{'A['w]} } -->
   ["wf"]   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x] >- fun_prop{w. 'A['w]} } -->
   ["antecedent"] sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x] >- member{'z; 's} } -->
   ["main"] sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x]; w: 'A['z] >- 'C['x] } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x] >- 'C['x] }

(*
 * This is a restricted formula.
 *)
interactive dall_res2 {| intro_resource [] |} 'H 'w 'x :
   ["wf"]   sequent ['ext] { 'H; w: set; x: set >- "type"{'B['w; 'x]} } -->
   ["wf"]   sequent ['ext] { 'H >- fun_set{w. 'A['w]} } -->
   ["main"] sequent ['ext] { 'H >- restricted{z, y. 'B['z; 'y]} } -->
   sequent ['ext] { 'H >- restricted{z. "dall"{'A['z]; y. 'B['z; 'y]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
