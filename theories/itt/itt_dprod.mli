(*
 * Rules for dependent product.
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
include Itt_struct
include Itt_subtype

open Refiner.Refiner.Term

open Tactic_type.Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(* declare prod{'A; 'B} *)
declare prod{'A; x. 'B['x]}
declare pair{'a; 'b}
declare spread{'e; u, v. 'b['u; 'v]}

declare fst{'e}
declare snd{'e}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_prod
prec prec_spread

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Reduction on spread:
 * spread(u, v; a, b. c[a, b]) <--> c[u, v]
 *)
rewrite reduceSpread : spread{'u, 'v; a, b. 'c['a; 'b]} <--> 'c['u; 'v]

rewrite unfoldFst : fst{'e} <--> spread{'e; u, v. 'u}
rewrite unfoldSnd : fst{'e} <--> spread{'e; u, v. 'v}

rewrite reduceFst : fst{pair{'a; 'b}} <--> 'a
rewrite reduceSnd : snd{pair{'a; 'b}} <--> 'b

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext x:A # B
 * by productFormation A x
 * H >- A = A in Ui
 * H, x:A >- Ui ext B
 *)
rule productFormation 'H 'A 'x :
   sequent [squash] { 'H >- member{univ[i:l]; 'A} } -->
   sequent ['ext] { 'H; x: 'A >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H >- x1:A1 # B1 = x2:A2 # B2 in Ui
 * by productEquality y
 * H >- A1 = A2 in Ui
 * H, y:A1 >- B1[y] = B2[y] in Ui
 *)
rule productEquality 'H 'y :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent ['ext] { 'H >- x1:'A1 * 'B1['x1] = x2:'A2 * 'B2['x2] in univ[i:l] }

(*
 * Typehood.
 *)
rule productType 'H 'x :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H; x: 'A1 >- "type"{'A2['x]} } -->
   sequent ['ext] { 'H >- "type"{.y:'A1 * 'A2['y]} }

(*
 * H >- x:A * B ext (a, b)
 * by pairFormation a y
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
rule pairFormation 'H 'a 'y :
   sequent [squash] { 'H >- member{'A; 'a} } -->
   sequent ['ext] { 'H >- 'B['a] } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- x:'A * 'B['x] }

(*
 * H >- (a1, b1) = (a2, b2) in x:A * B
 * by pairEquality y
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B[a1]
 * H, y:A >- B[y] = B[y] in Ui
 *)
rule pairEquality 'H 'y :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B['a1] } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- ('a1, 'b1) = ('a2, 'b2) in x:'A * 'B['x] }

(*
 * H, x:A * B[x], J[x] >- T[x] ext spread(x; u, v. t[u, v])
 * by productElimination u v
 * H, x:A * B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
rule productElimination 'H 'J 'z 'u 'v :
   sequent ['ext] { 'H; z: x:'A * 'B['x]; u: 'A; v: 'B['u]; 'J['u, 'v] >- 'T['u, 'v] } -->
   sequent ['ext] { 'H; z: x:'A * 'B['x]; 'J['z] >- 'T['z] }

(*
 * H >- spread(e1; u1, v1. b1) = spread(e2; u2, v2. b2) in T[e1]
 * by spreadEquality (w:A * B)
 * H >- e1 = e2 in w:A * B
 * H, u:A, v: B[u], a: e1 = (u, v) in w:A * B >- b1[u; v] = b2[u; v] in T[u, v]
 *)
rule spreadEquality 'H lambda{z. 'T['z]} (w:'A * 'B['w]) 'u 'v 'a :
   sequent [squash] { 'H >- 'e1 = 'e2 in w:'A * 'B['w] } -->
   sequent [squash] { 'H; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >-
             'b1['u; 'v] = 'b2['u; 'v] in 'T['u, 'v] } -->
   sequent ['ext] { 'H >- spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T['e1] }

(*
 * H >- a1:A1 * B1 <= a2:A2 * B2
 * by functionSubtype
 *
 * H >- A1 <= A2
 * H, a: A1 >- B1[a] <= B2[a]
 *)
rule productSubtype 'H 'a :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H; a: 'A1 >- subtype{'B1['a]; 'B2['a]} } -->
   sequent ['ext] { 'H >- subtype{ (a1:'A1 * 'B1['a1]); (a2:'A2 * 'B2['a2]) } }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val dprod_term : term
val is_dprod_term : term -> bool
val dest_dprod : term -> string * term * term
val mk_dprod_term : string -> term -> term -> term

val prod_term : term
val is_prod_term : term -> bool
val dest_prod : term -> term * term
val mk_prod_term : term -> term -> term

val pair_term : term
val is_pair_term : term -> bool
val dest_pair : term -> term * term
val mk_pair_term : term -> term -> term

val spread_term : term
val is_spread_term : term -> bool
val dest_spread : term -> string * string * term * term
val mk_spread_term : string -> string -> term -> term -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
