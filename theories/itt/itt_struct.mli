(*
 * Structural rules.
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
 *
 *)

include Itt_equal

open Refiner.Refiner.Term

open Tactic_type.Tacticals
open Tactic_type.Sequent


(*
 * H; x: A; J >- A ext x
 * by hypothesis
 *)
rule hypothesis 'H 'J 'x :
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'A }

(*
(*
 * H, x: A, J >- A ext t
 * by thin
 * H, J >- A ext t
 *)
rule thin 'H 'J :
   sequent ['ext] { 'H; 'J >- 'C } -->
   sequent ['ext] { 'H; x: 'A; 'J >- 'C }

(*
 * H, J >- T ext t[s]
 * by cut S
 * H, J >- S ext s
 * H, x: S, J >- T ext t[x]
 *)
rule cut 'H 'J 'S 'x :
   sequent ['ext] { 'H; 'J >- 'S } -->
   sequent ['ext] { 'H; x: 'S; 'J >- 'T } -->
   sequent ['ext] { 'H; 'J >- 'T }
*)

(*
 * H >- T
 * by introduction t
 * H >- t = t in T
 *)
rule introduction 'H 't :
   sequent [squash] { 'H >- 't IN 'T } -->
   sequent ['ext] { 'H >- 'T }

(*
 * H >- T1[t1] ext t
 * by substitution (t1 = t2 in T2) lambda(x. T1[x])
 * H >- t1 = t2 in T2
 * H >- T1[t2]
 * H, x: T2 >- T1[x] = T1[x] in type
 *)
rule substitution 'H ('t1 = 't2 in 'T2) bind{x. 'T1['x]} :
   sequent [squash] { 'H >- 't1 = 't2 in 'T2 } -->
   sequent ['ext] { 'H >- 'T1['t2] } -->
   sequent [squash] { 'H; x: 'T2 >- "type"{'T1['x]} } -->
   sequent ['ext] { 'H >- 'T1['t1] }

(*
 * H, x: A, J >- T
 * by hypothesesReplacement B
 * H, x:B, J >- T
 * H, x: A, J >- A = B in type
 *)
rule hypReplacement 'H 'J 'B univ[i:l] :
   sequent ['ext] { 'H; x: 'B; 'J['x] >- 'T['x] } -->
   sequent [squash] { 'H; x: 'A; 'J['x] >- 'A = 'B in univ[i:l] } -->
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'T['x] }

(*
 * H; x: A[t1]; J[x] >> T1[x] ext t
 * by hypSubstitution (t1 = t2 in T2) bind(x. A[x])
 * H; x: A[t1]; J[x] >> t1 = t2 in T2
 * H; x: A[t2]; J[x] >> T1[x]
 * H, x: A[t1]; J[x]; z: T2 >> A[z] in type
 *)
rule hypSubstitution 'H 'J ('t1 = 't2 in 'T2) bind{y. 'A['y]} 'z :
   sequent [squash] { 'H; x: 'A['t1]; 'J['x] >- 't1 = 't2 in 'T2 } -->
   sequent ['ext]  { 'H; x: 'A['t2]; 'J['x] >- 'T1['x] } -->
   sequent [squash] { 'H; x: 'A['t1]; 'J['x]; z: 'T2 >- "type"{'A['z]} } -->
   sequent ['ext]  { 'H; x: 'A['t1]; 'J['x] >- 'T1['x] }

(*
 * Typehood.
 *)
rule equalityTypeIsType 'H 'a 'b :
   sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- "type"{'T} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval nthHypT : int -> tactic
topval thinT : int -> tactic
topval thinAllT : int -> int -> tactic
topval assertT : term -> tactic
(* do not assert if already have the right conclusion *)
topval tryAssertT : term -> tactic -> tactic -> tactic
topval assertAtT : int -> term -> tactic
topval dupT : tactic
topval useWitnessT : term -> tactic

topval substT : term -> int -> tactic
topval hypSubstT : int -> int -> tactic
topval revHypSubstT : int -> int -> tactic

topval replaceHypT : term -> int -> tactic

topval equalTypeT : term -> term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
