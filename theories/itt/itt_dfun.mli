(*
 * Dependent functions.
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
include Itt_rfun

open Refiner.Refiner.Term

open Tactic_type.Tacticals
open Tactic_type.Conversionals

rewrite reduceEta (x: 'A -> 'B['x]) : ('f = 'f in (x: 'A -> 'B['x])) -->
   lambda{x. 'f 'x} <--> 'f

rewrite unfold_dfun : (x: 'A -> 'B['x]) <--> ({ f | x: 'A -> 'B['x] })

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext a:A -> B
 * by functionFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
rule functionFormation 'H 'a 'A :
   sequent [squash] { 'H >- member{univ[i:l]; 'A} } -->
   sequent ['ext] { 'H; a: 'A >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H >- (a1:A1 -> B1[a1]) = (a2:A2 -> B2[a2]) in Ui
 * by functionEquality x
 *
 * H >- A1 = A2 in Ui
 * H, x: A1 >- B1[x] = B2[x] in Ui
 *)
rule functionEquality 'H 'x :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   sequent [squash] { 'H; x: 'A1 >- 'B1['x] = 'B2['x] in univ[i:l] } -->
   sequent ['ext] { 'H >- (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l] }

(*
 * Typehood.
 *)
rule functionType 'H 'x :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H; x: 'A1 >- "type"{'B1['x]} } -->
   sequent ['ext] { 'H >- "type"{. a1:'A1 -> 'B1['a1] } }

(*
 * H >- a:A -> B[a] ext lambda(z. b[z])
 * by lambdaFormation Ui z
 *
 * H >- A = A in Ui
 * H, z: A >- B[z] ext b[z]
 *)
rule lambdaFormation 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H; z: 'A >- 'B['z] } -->
   sequent ['ext] { 'H >- a:'A -> 'B['a] }

(*
 * H >- lambda(a1. b1[a1]) = lambda(a2. b2[a2]) in a:A -> B
 * by lambdaEquality Ui x
 *
 * H >- A = A in Ui
 * H, x: A >- b1[x] = b2[x] in B[x]
 *)
rule lambdaEquality 'H 'x :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'A >- 'b1['x] = 'b2['x] in 'B['x] } -->
   sequent ['ext] { 'H >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in a:'A -> 'B['a] }

(*
 * H >- f = g in x:A -> B
 * by functionExtensionality Ui (y:C -> D) (z:E -> F) u
 *
 * H, u:A >- f(u) = g(u) in B[u]
 * H >- A = A in Ui
 * H >- f = f in y:C -> D
 * H >- g = g in z:E -> F
 *)
rule functionExtensionality 'H (y:'C -> 'D['y]) (z:'E -> 'F['z]) 'u :
   sequent [squash] { 'H; u: 'A >- ('f 'u) = ('g 'u) in 'B['u] } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- 'f = 'f in y:'C -> 'D['y] } -->
   sequent [squash] { 'H >- 'g = 'g in z:'E -> 'F['z] } -->
   sequent ['ext] { 'H >- 'f = 'g in x:'A -> 'B['x] }

(*
 * H, f: (x:A -> B), J[x] >- T[f] t[f, f a, it]
 * by functionElimination i a y v
 *
 * H, f: (x:A -> B), J[x] >- a = a in A
 * H, f: (x:A -> B), J[x], y: B[a], v: y = f(a) in B[a] >- T[f] ext t[f, y, v]
 *)
rule functionElimination 'H 'J 'f 'a 'y 'v :
   sequent [squash] { 'H; f: x:'A -> 'B['x]; 'J['f] >- member{'A; 'a} } -->
   sequent ['ext] { 'H; f: x:'A -> 'B['x]; 'J['f]; y: 'B['a]; v: 'y = ('f 'a) in 'B['a] >- 'T['f] } -->
   sequent ['ext] { 'H; f: x:'A -> 'B['x]; 'J['f] >- 'T['f] }

(*
 * H >- (f1 a1) = (f2 a2) in B[a1]
 * by applyEquality (x:A -> B[x])
 *
 * H >- f1 = f2 in x:A -> B[x]
 * H >- a1 = a2 in A
 *)
rule applyEquality 'H (x:'A -> 'B['x]) :
   sequent [squash] { 'H >- 'f1 = 'f2 in x:'A -> 'B['x] } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- ('f1 'a1) = ('f2 'a2) in 'B['a1] }

rule applyMember 'H (x:'A -> 'B['x]) :
   sequent [squash] { 'H >- member{. x:'A -> 'B['x]; 'f1} } -->
   sequent [squash] { 'H >- member{'A; 'a1} } -->
   sequent ['ext] { 'H >- member{'B['a1]; .'f1 'a1} }

topval applyEquality' : term -> tactic
topval applyMember' : term -> tactic

(*
 * H >- a1:A1 -> B1 <= a2:A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H, a: A1 >- B1[a] <= B2[a]
 *)
rule functionSubtype 'H 'a :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['prop] { 'H >- subtype{ (a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2]) } }

(*
(*
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; J[x] >- T[x]
 * by function_subtypeElimination i
 *
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; y: A2 <= A1; z: a:A2 -> B2[a] <= B1[a]; J[x] >- T[x]
 *)
rule function_subtypeElimination 'H 'J 'x 'y 'z 'a :
   sequent { 'H;
             x: subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])};
             'J['x];
             y: subtype{'A2; 'A1};
             z: a:'A2 -> subtype{'B1['a]; 'B2['a]}
             >- 'T['x]
           } -->
   sequent { 'H; x: subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])}; 'J['x] >- 'T['x] }
*)

(*
 * JYH: this rule assumes an intentional type theory, and the rule doesn't belong
 * in this module.
 *
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; J[x] >- T[x]
 * by function_equalityElimination
 *
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; y: A1 = A2 in Ui; z: a:A1 -> B1[a] = B2[a] in Ui; J[x] >- T[x]
rule function_equalityElimination 'H 'J 'x 'y 'z 'a :
   sequent { 'H;
             x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l];
             'J['x];
             y: 'A1 = 'A2 in univ[i:l];
             z: a:'A1 -> ('B1['a] = 'B2['a] in univ[i:l])
             >- 'T['x]
           } -->
   sequent { 'H; x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l]; 'J['x] >- 'T['x] }
 *)

topval dfun_extensionalityT : term -> term -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
