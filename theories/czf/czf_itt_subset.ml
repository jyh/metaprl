(*
 * Subset predicate.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2000 Jason Hickey, Caltech
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
 * jyh@cs.caltech.edu
 *)

include Czf_itt_pre_theory

declare subset{'s1; 's2}

prim_rw unfold_subset : subset{'s1; 's2} <--> dall{'s1; x. member{'x; 's2}}

prec prec_subset

dform subset_df : parens :: "prec"[prec_subset] :: subset{'s1; 's2} =
   slot{'s1} `" " Nuprl_font!subseteq `" " slot{'s2}

interactive subset_type {| intro_resource [] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- "type"{subset{'s1; 's2}} }

interactive subset_intro {| intro_resource [] |} 'H 'x :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   ["main"] sequent ['ext] { 'H; x: set; y: member{'x; 's1} >- member{'x; 's2} } -->
   sequent ['ext] { 'H >- subset{'s1; 's2} }

interactive subset_elim {| elim_resource [] |} 'H 'J 's 'z :
   ["wf"] sequent [squash] { 'H; x: subset{'s1; 's2}; 'J['x] >- isset{'s2} } -->
   ["antecedent"] sequent ['ext] { 'H; x: subset{'s1; 's2}; 'J['x] >- member{'s; 's1} } -->
   ["main"] sequent ['ext] { 'H; x: subset{'s1; 's2}; 'J['x]; z: member{'s; 's2} >- 'C['x] } -->
   sequent ['ext] { 'H; x: subset{'s1; 's2}; 'J['x] >- 'C['x] }

interactive subset_res {| intro_resource [] |} 'H :
   ["wf"] sequent [squash] { 'H >- isset{'s1} } -->
   ["wf"] sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- restricted{subset{'s1; 's2}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
