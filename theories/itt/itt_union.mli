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

extends Itt_equal
extends Itt_struct
extends Itt_subtype

open Refiner.Refiner.Term

open Tactic_type.Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare \union{'A; 'B}
declare inl{'x}
declare inr{'x}
declare decide{'x; y. 'a['y]; z. 'b['z]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Reduction on decide.
 * decide(inl x; u. l[u]; v. r[v]) <--> l[x]
 * decide(inr x; u. l[u]; v. r[v]) <--> r[x]
 *)
rewrite reduceDecideInl : decide{inl{'x}; u. 'l['u]; v. 'r['v]} <--> 'l['x]
rewrite reduceDecideInr : decide{inr{'x}; u. 'l['u]; v. 'r['v]} <--> 'r['x]

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_inl
prec prec_union

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext A + B
 * by unionFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
rule unionFormation :
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H >- A1 + B1 = A2 + B2 in Ui
 * by unionEquality
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
rule unionEquality :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[i:l] } -->
   sequent ['ext] { 'H >- 'A1 + 'B1 = 'A2 + 'B2 in univ[i:l] }


(*
 * Typehood.
 *)
rule unionType :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{. 'A + 'B } }

(*
 * H >- A + B ext inl a
 * by inlFormation
 * H >- A
 * H >- B = B in Ui
 *)
rule inlFormation :
   sequent ['ext] { 'H >- 'A } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- 'A + 'B }

(*
 * H >- A + B ext inl a
 * by inrFormation
 * H >- B
 * H >- A = A in Ui
 *)
rule inrFormation :
   sequent ['ext] { 'H >- 'B } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- 'A + 'B }

(*
 * H >- inl a1 = inl a2 in A + B
 * by inlEquality
 * H >- a1 = a2 in A
 * H >- B = B in Ui
 *)
rule inlEquality :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- inl{'a1} = inl{'a2} in 'A + 'B }

(*
 * H >- inr b1 = inr b2 in A + B
 * by inrEquality
 * H >- b1 = b2 in B
 * H >- A = A in Ui
 *)
rule inrEquality :
   sequent [squash] { 'H >- 'b1 = 'b2 in 'B } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- inr{'b1} = inr{'b2} in 'A + 'B }

(*
 * H, x: A + B, J[x] >- T[x] ext decide(x; u. 'left['u]; v. 'right['v])
 * by unionElimination x u v
 * H, x: A # B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
rule unionElimination 'H :
   sequent ['ext] { 'H; x: 'A + 'B; u: 'A; 'J[inl{'u}] >- 'T[inl{'u}] } -->
   sequent ['ext] { 'H; x: 'A + 'B; v: 'B; 'J[inr{'v}] >- 'T[inr{'v}] } -->
   sequent ['ext] { 'H; x: 'A + 'B; 'J['x] >- 'T['x] }

(*
 * H >- decide(e1; u1. l1[u1]; v1. r1[v1]) = decide(e2; u2. l2[u2]; v2. r2[v2]) in T[e1]
 * by unionEquality bind(z. T[z]) (A + B) u v w
 * H >- e1 = e2 in A + B
 * H, u:A, w: e1 = inl u in A + B >- l1[u] = l2[u] in T[inl u]
 * H, v:A, w: e1 = inr v in A + B >- r1[v] = r2[v] in T[inr v]
 *)
rule decideEquality bind{z. 'T['z]} ('A + 'B) :
   sequent [squash] { 'H >- 'e1 = 'e2 in 'A + 'B } -->
   sequent [squash] { 'H; u: 'A; w: 'e1 = inl{'u} in 'A + 'B >- 'l1['u] = 'l2['u] in 'T[inl{'u}] } -->
   sequent [squash] { 'H; v: 'B; w: 'e1 = inr{'v} in 'A + 'B >- 'r1['v] = 'r2['v] in 'T[inr{'v}] } -->
   sequent ['ext] { 'H >- decide{'e1; u1. 'l1['u1]; v1. 'r1['v1]} =
                   decide{'e2; u2. 'l2['u2]; v2. 'r2['v2]} in
                   'T['e1] }

(*
 * H >- A1 + B1 <= A2 + B2
 * by unionSubtype
 *
 * H >- A1 <= A2
 * H >- B1 <= B2
 *)
rule unionSubtype :
   sequent [squash] { 'H >- \subtype{'A1; 'A2} } -->
   sequent [squash] { 'H >- \subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- \subtype{ ('A1 + 'B1); ('A2 + 'B2) } }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val union_term : term
val is_union_term : term -> bool
val dest_union : term -> term * term
val mk_union_term : term -> term -> term

val inl_term : term
val is_inl_term : term -> bool
val dest_inl : term -> term
val mk_inl_term : term -> term

val inr_term : term
val is_inr_term : term -> bool
val dest_inr : term -> term
val mk_inr_term : term -> term

val decide_term : term
val is_decide_term : term -> bool
val dest_decide : term -> term * string * term * string * term
val mk_decide_term : term -> string -> term -> string -> term -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
