(*
 * W types.
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

include Itt_equal
include Itt_rfun

open Opname
open Refiner.Refiner.Term

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * W type is type of trees   (type w = a:A * (B[a] -> w))
 *)
declare w{'A; x. 'B['x]}

(*
 * Trees.  Each node has a label 'a, and a function to
 * compute the children 'f.
 *)
declare tree{'a; 'f}

(*
 * Induction over trees.
 *)
declare tree_ind{'z; a, f, g. 'body['a; 'f; 'g]}

(*
 * Reduction rule.
 * The g part composes the label with an application to f.
 *)
rewrite reduce_tree_ind :
   tree_ind{tree{'a1; 'f1}; a2, f2, g2. 'body['a2; 'f2; 'g2]}
   <--> 'body['a1; 'f1; lambda{a. lambda{b. tree_ind{.'f1 'a 'b; a2, f2, g2. 'body['a2; 'f2; 'g2]}}}]

(*
 * Precedence of display form.
 *)
prec prec_w
prec prec_tree_ind

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext W(x:A; B[x])
 * by wFormation A x
 * H >- A = A in Ui
 * H, x:A >- Ui ext B
 *)
rule wFormation 'H 'A 'x :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   sequent ['ext] { 'H; x: 'A >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- W(x1:A1; B1) = W(x2:A2; B2) in Ui
 * by wEquality y
 * H >- A1 = A2 in Ui
 * H, y:A1 >- B1[y] = B2[y] in Ui
 *)
rule wEquality 'H 'y :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; y: 'A1 >- 'B1['y] = 'B2['y] in univ[@i:l] } -->
   sequent ['ext] { 'H >- w{'A1; x1. 'B1['x1]} = w{'A2; x2. 'B2['x2]} in univ[@i:l] }

(*
 * Typehood.
 *)
rule wType 'H 'x :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H; x: 'A1 >- "type"{'A2['x]} } -->
   sequent ['ext] { 'H >- "type"{.w{'A1; y.'A2['y]}} }

(*
 * H >- W(x:A; B[x]) ext tree(a, f)
 * by treeFormation a y
 * H >- a = a in A
 * H >- B[a] -> W(x:A; B[x]) ext f
 * H, y:A >- B[y] = B[y] in Ui
 *)
rule treeFormation 'H 'a 'y :
   sequent [squash] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'B['a] -> w{'A; x. 'B['x]} } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- w{'A; x. 'B['x]} }

(*
 * H >- tree(a1, b1) = tree(a2, b2) in W(x:A; B)
 * by treeEquality y
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B[a1] -> W(x:A; B)
 * H, y:A >- B[y] = B[y] in Ui
 *)
rule treeEquality 'H 'y :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B['a1] -> w{'A; x. 'B['x]} } -->
   sequent [squash] { 'H; y: 'A >- "type"{'B['y]} } -->
   sequent ['ext] { 'H >- tree{'a1; 'b1} = tree{'a2; 'b2} in w{'A; x. 'B['x]} }

(*
 * H, x:W(y:A; B[y]), J[x] >- T[x] ext spread(x; u, v. t[u, v])
 * by wElimination u v
 * H, x:W(y:A; B[y]), u:A, v:B[u] -> W(y:A; B[y]), J[tree(u, v)] >- T[tree(u, v)] ext t[u, v]
 *)
rule wElimination 'H 'J 'z 'a 'f 'g 'a2 'b2 :
   sequent ['ext] { 'H;
                    z: w{'A; x. 'B['x]};
                    'J['z];
                    a: 'A;
                    f: 'B['a] -> w{'A; x. 'B['x]};
                    g: a2: 'A -> b2: 'B['a2] -> 'T['f 'b2]
                  >- 'T[tree{'a; 'f}]
                  } -->
   sequent ['ext] { 'H; z: w{'A; x. 'B['x]}; 'J['z] >- 'T['z] }

(*
 * Equality on tree induction forms.
 *)
rule tree_indEquality 'H (w{'A; x. 'B['x]}) 'a 'f 'g :
   sequent [squash] { 'H >- 'z1 = 'z2 in w{'A; x. 'B['x]} } -->
   sequent [squash] { 'H; a: 'A; f: 'B['a] -> w{'A; x. 'B['x]}; g: a: 'A -> 'B['a] -> 'T >-
      'body1['a; 'f; 'g] = 'body2['a; 'f; 'g] in 'T } -->
   sequent ['ext] { 'H >- tree_ind{'z1; a1, f1, g1. 'body1['a1; 'f1; 'g1]}
                          = tree_ind{'z2; a2, f2, g2. 'body2['a2; 'f2; 'g2]}
                          in 'T }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val w_term : term
val w_opname :opname
val is_w_term : term -> bool
val dest_w : term -> string * term * term
val mk_w_term : string -> term -> term -> term

val tree_term : term
val tree_opname : opname
val is_tree_term : term -> bool
val dest_tree : term -> term * term
val mk_tree_term : term -> term -> term

val tree_ind_term : term
val tree_ind_opname : opname
val is_tree_ind_term : term -> bool
val dest_tree_ind : term -> string * string * string * term * term
val mk_tree_ind_term :  string -> string -> string -> term -> term -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
