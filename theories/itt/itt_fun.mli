(*
 * Simplifications for undependent functions.
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

extends Itt_equal
extends Itt_dfun

open Refiner.Refiner.TermType

open Tactic_type.Tacticals
open Tactic_type.Conversionals

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_fun : ('A -> 'B) <--> (x: 'A -> 'B)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext A -> B
 * by independentFunctionFormation
 *
 * H >- Ui ext A
 * H >- Ui ext B
 *)
rule independentFunctionFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H >- (A1 -> B1) = (A2 -> B2) in Ui
 * by independentFunctionEquality
 *
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
rule independentFunctionEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- ('A1 -> 'B1) = ('A2 -> 'B2) in univ[i:l] }

(*
 * Typehood.
 *)
rule independentFunctionType 'H 'x :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H; x: 'A1 >- "type"{'B1} } -->
   sequent ['ext] { 'H >- "type"{. 'A1 -> 'B1 } }

(*
 * H >- a:A -> B[a] ext lambda(z. b[z])
 * by lambdaFormation Ui z
 *
 * H >- A = A in Ui
 * H, z: A >- B[z] ext b[z]
 *)
rule independentLambdaFormation 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H; z: 'A >- 'B } -->
   sequent ['ext] { 'H >- 'A -> 'B }

(*
 * H >- lambda(a1. b1[a1]) = lambda(a2. b2[a2]) in a:A -> B
 * by lambdaEquality Ui x
 *
 * H >- A = A in Ui
 * H, x: A >- b1[x] = b2[x] in B[x]
 *)
rule independentLambdaEquality 'H 'x :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'A >- 'b1['x] = 'b2['x] in 'B } -->
   sequent ['ext] { 'H >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in 'A -> 'B }

(*
 * H, f: A -> B, J[x] >- T[x]                   ext t[f, f a]
 * by independentFunctionElimination i y
 *
 * H, f: A -> B, J >- A                         ext a
 * H, f: A -> B, J[x], y: B >- T[x]             ext t[f, y]
 *)
rule independentFunctionElimination 'H 'J 'f 'y :
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'A } -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f]; y: 'B >- 'T['f] } -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'T['f] }

(*
 * Explicit function elimination.
 *)
rule independentFunctionElimination2 'H 'J 'f 'y 'z 'a :
   sequent [squash] { 'H; f: 'A -> 'B; 'J['f] >- 'a in 'A } -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f]; y: 'B; z: 'y = ('f 'a) in 'B >- 'T['f] } -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'T['f] }

(*
 * H >- (f1 a1) = (f2 a2) in B[a1]
 * by applyEquality (x:A -> B[x])
 *
 * H >- f1 = f2 in x:A -> B[x]
 * H >- a1 = a2 in A
 *)
rule independentApplyEquality 'H ('A -> 'B) :
   sequent [squash] { 'H >- 'f1 = 'f2 in 'A -> 'B } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- ('f1 'a1) = ('f2 'a2) in 'B }

(*
 * H >- A1 -> B1 <= A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H >- B1 <= B2
 *)
rule independentFunctionSubtype 'H :
   sequent [squash] { 'H >- \subtype{'A2; 'A1} } -->
   sequent [squash] { 'H >- \subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- \subtype{ ('A1 -> 'B1); ('A2 -> 'B2) } }

topval fnExtensionalityT : term -> term -> tactic
topval fnExtenT : term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
