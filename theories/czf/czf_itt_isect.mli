(*
 * Intersection of two sets.
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

include Czf_itt_set

open Tactic_type.Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "isect"{'s1; 's2}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_isect : isect{'s1; 's2} <-->
   set_ind{'s1; a1, f1, g1.
      set_ind{'s2; a2, f2, g2.
         collect{.(z: 'a1 * 'a2); x. spread{'x; a, b.

rewrite reduce_union : union{collect{'t1; x1. 'f1['x1]};
                             collect{'t2; x2. 'f2['x2]}} <-->
   collect{.Itt_union!union{'t1; 't2}; x. decide{'x; z. 'f1['z]; z. 'f2['z]}}

val fold_union : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Union is a set.
 *)
rule union_isset 'H :
   sequent ['ext] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- isset{union{'s1; 's2}} }

(*
 * Membership in a union.
 *)
rule union_member_intro_left 'H :
   sequent ['ext] { 'H >- member{'x; 's1} } -->
   sequent ['ext] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- member{'x; union{'s1; 's2}} }

rule union_member_intro_right 'H :
   sequent ['ext] { 'H >- member{'x; 's2} } -->
   sequent ['ext] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- member{'x; union{'s1; 's2}} }

(*
 * This is the elimination form we want,
 * but it requires extensional equality.
rule union_member_elim 'H 'J :
   sequent ['ext] { 'H; x: member{'y; 's1}; 'J['x] >- 'T['x] } -->
   sequent ['ext] { 'H; x: member{'y; 's2}; 'J['x] >- 'T['x] } -->
   sequent ['ext] { 'H; x: member{'y; union{'s1; 's2}}; 'J['x] >- 'T['x] }
 *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
