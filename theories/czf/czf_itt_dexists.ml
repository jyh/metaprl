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

include Czf_itt_sep
include Czf_itt_set_ind

open Printf
open Mp_debug

open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Tactic_type.Sequent
open Var

open Itt_logic
open Itt_rfun

let _ =
   show_loading "Loading Czf_itt_dexists%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "dexists"{'T; x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_dexists : "dexists"{'s; x. 'A['x]} <-->
   set_ind{'s; T, f, g. x: 'T * 'A['f 'x]}

interactive_rw reduce_dexists : "dexists"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T * 'A['f['t]])

let reduce_info =
   [<< "dexists"{collect{'T; x. 'f['x]}; y. 'A['y]} >>, reduce_dexists]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform dexists_df : mode[prl] :: parens :: "prec"[prec_lambda] :: "dexists"{'s; x. 'A} =
   pushm[0] Nuprl_font!"exists" slot{'x} " " Nuprl_font!member " " slot{'s} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive dexists_type {| intro_resource [] |} 'H 'y :
   ["wf"] sequent [squash] { 'H >- isset{'s} } -->
   ["wf"] sequent [squash] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."dexists"{'s; x. 'A['x]}} }

(*
 * Intro.
 *)
interactive dexists_intro {| intro_resource [] |} 'H 'z 'w :
   ["wf"] sequent [squash] { 'H; w: set >- "type"{'A['w]} } -->
   ["wf"] sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   ["main"] sequent ['ext] { 'H >- member{'z; 's} } -->
   ["antecedent"] sequent ['ext] { 'H >- 'A['z] } -->
   sequent ['ext] { 'H >- "dexists"{'s; x. 'A['x]} }

(*
 * Elimination.
 *)
interactive dexists_elim {| elim_resource [] |} 'H 'J 'x 'z 'v 'w :
   ["wf"] sequent ['ext] { 'H; x: "dexists"{'s; y. 'A['y]}; 'J['x] >- isset{'s} } -->
   ["wf"] sequent ['ext] { 'H; x: "dexists"{'s; y. 'A['y]}; 'J['x]; z: set >- "type"{'A['z]} } -->
   ["wf"] sequent ['ext] { 'H; x: "dexists"{'s; y. 'A['y]}; 'J['x] >- fun_prop{z. 'A['z]} } -->
   ["main"] sequent ['ext] { 'H;
                    x: "dexists"{'s; y. 'A['y]};
                    'J['x];
                    z: set;
                    v: member{'z; 's};
                    w: 'A['z]
                    >- 'C['x]
                  } -->
   sequent ['ext] { 'H; x: "dexists"{'s; y. 'A['y]}; 'J['x] >- 'C['x] }

(*
 * This is a restricted formula.
 *)
interactive dexists_res2 {| intro_resource [] |} 'H 'w 'x :
   ["wf"]   sequent ['ext] { 'H >- isset{'A} } -->
   ["wf"]   sequent ['ext] { 'H; x: set >- "type"{'B['x]} } -->
   ["main"] sequent ['ext] { 'H >- restricted{y. 'B['y]} } -->
   sequent ['ext] { 'H >- restricted{."dexists"{'A; y. 'B['y]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
