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
include Itt_dprod
include Itt_struct

open Tactic_type.Tacticals

(*
 * The independent product is defined as a dependent product.
 *)
rewrite unfoldProd : ('A * 'B) <--> (x: 'A * 'B)

(*
 * H >- Ui ext A * B
 * by independentProductFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
rule independentProductFormation 'H :
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H >- A1 * B1 = A2 * B2 in Ui
 * by independentProductEquality
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
rule independentProductEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- 'A1 * 'B1 = 'A2 * 'B2 in univ[i:l] }

(*
 * Typehood.
 *)
rule independentProductType 'H :
   sequent [squash] { 'H >- "type"{'A1} } -->
   sequent [squash] { 'H >- "type"{'A2} } -->
   sequent ['ext] { 'H >- "type"{.'A1 * 'A2} }

(*
 * H >- A * B ext (a, b)
 * by independentPairFormation a y
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
rule independentPairFormation 'H :
   sequent ['ext] { 'H >- 'A } -->
   sequent ['ext] { 'H >- 'B } -->
   sequent ['ext] { 'H >- 'A * 'B }

(*
 * H, A * B, J >- T ext t
 * by independentProductElimination
 * H, A * B, u: A, v: B, J >- T ext t
 *)
rule independentProductElimination 'H 'J 'z 'u 'v :
   sequent ['ext] { 'H; z: 'A * 'B; u: 'A; v: 'B; 'J['u, 'v] >- 'T['u, 'v] } -->
   sequent ['ext] { 'H; z: 'A * 'B; 'J['z] >- 'T['z] }

(*
 * H >- (a1, b1) = (a2, b2) in A * B
 * by independentPairEquality
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B
 *)
rule independentPairEquality 'H :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B } -->
   sequent ['ext] { 'H >- ('a1, 'b1) = ('a2, 'b2) in 'A * 'B }

(*
 * H >- A1 -> B1 <= A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H >- B1 <= B2
 *)
rule independentProductSubtype 'H :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 * 'B1); ('A2 * 'B2) } }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
