(*
 * Simple recursive type.
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

open Refiner.Refiner.Term

extends Itt_equal
extends Itt_prec
extends Itt_subtype

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare srec{T. 'B['T]}
declare srecind{'a; p, h. 'g['p; 'h]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_srecind : srecind{'a; p, h. 'g['p; 'h]} <-->
   'g[lambda{a. srecind{'a; p, h. 'g['p; 'h]}}; 'a]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext srec(T. B[T])
 * by srecFormation T
 *
 * H, T: Ui >- Ui ext B[T]
 *)
rule srecFormation 'H 'T :
   sequent ['ext] { 'H; T: univ[i:l] >- univ[i:l] } -->
   sequent ['ext] { 'H >- univ[i:l] }

(*
 * H >- srec(T1. B1[T1]) = srec(T2. B2[T2]) in Ui
 * by srecEquality T S1 S2 z
 *
 * H; T: Ui >- B1[T] = B2[T] in Ui
 * H; S1: Ui; S2: Ui; z: subtype(S1; S2) >- subtype(B1[S1]; B1[S2])
 *)
rule srecEquality 'H 'T 'S1 'S2 'z :
   sequent [squash] { 'H; T: univ[i:l] >- 'B1['T] = 'B2['T] in univ[i:l] } -->
   sequent [squash] { 'H; S1: univ[i:l]; S2: univ[i:l]; z: \subtype{'S1; 'S2} >- \subtype{'B1['S1]; 'B1['S2]} } -->
   sequent ['ext] { 'H >- srec{T1. 'B1['T1]} = srec{T2. 'B2['T2]} in univ[i:l] }

(*
 * H >- srec(T. B[T]) ext g
 * by srec_memberFormation
 *
 * H >- B[srec(T. B[T])] ext g
 * H >- srec(T. B[T]) = srec(T. B[T]) in Ui
 *)
rule srec_memberFormation 'H :
   sequent ['ext] { 'H >- 'B[srec{T. 'B['T]}] } -->
   sequent [squash] { 'H >- "type"{srec{T. 'B['T]}} } -->
   sequent ['ext] { 'H >- srec{T. 'B['T]} }

(*
 * H >- x1 = x2 in srec(T. B[T])
 * by srec_memberEquality
 *
 * H >- x1 = x2 in B[srec(T. B[T])]
 * H >- srec(T. B[T]) = srec(T. B[T]) in Ui
 *)
rule srec_memberEquality 'H :
   sequent [squash] { 'H >- 'x1 = 'x2 in 'B[srec{T. 'B['T]}] } -->
   sequent [squash] { 'H >- "type"{srec{T. 'B['T]}} } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in srec{T. 'B['T]} }

(*
 * H, x: srec(T. B[T]), J[x] >- C[x]
 * by srecElimination T1 u v w z
 *
 * H, x: srec(T. B[T]), J[x],
 *   T1: Ui,
 *   u: subtype(T1; srec(T. B[T])),
 *   w: v: T1 -> C[v],
 *   z: T[T1]
 * >- C[z]
 *)
rule srecElimination 'H 'J 'x srec{T. 'B['T]} 'T1 'u 'v 'w 'z univ[i:l] :
   sequent ['ext] { 'H; x: srec{T. 'B['T]}; 'J['x];
             T1: univ[i:l];
             u: \subtype{'T1; srec{T. 'B['T]}};
             w: v: 'T1 -> 'C['v];
             z: 'B['T1]
           >- 'C['z]
           } -->
   sequent ['ext] { 'H; x: srec{T. 'B['T]}; 'J['x] >- 'C['x] }

(*
 * H, x: srec(T. B[T]); J[x] >- C[x]
 * by srecUnrollElimination y u
 *
 * H, x: srec(T. B[T]); J[x]; y: B[srec(T. B[T])]; u: x = y in B[srec(T. B[T])] >- C[y]
 *)
rule srecUnrollElimination 'H 'J 'x 'y 'u :
   sequent ['ext] { 'H; x: srec{T. 'B['T]}; 'J['x]; y: 'B[srec{T. 'B['T]}]; u: 'x = 'y in 'B[srec{T. 'B['T]}] >- 'C['y] } -->
   sequent ['ext] { 'H; x: srec{T. 'B['T]}; 'J['x] >- 'C['x] }

(*
 * H >- srecind(r1; h1, z1. t1) = srecind(r2; h2, z2. t2) in S[r1]
 * by srecindEquality lambda(x. S[x]) srec(T. B[T]) T1 u v w z
 *
 * H >- r1 = r2 in srec(T. B[T])
 * H, T1: Ui, z: subtype(T1; srec(T. B[T])),
 *    v: w: T1 -> S[w], w: T[T1]
 *    >- t1[v; w] = t2[v; w] in S[w]
 *)
rule srecindEquality 'H lambda{x. 'S['x]} srec{T. 'B['T]} 'T1 'u 'v 'w 'z univ[i:l] :
   sequent [squash] { 'H >- 'r1 = 'r2 in srec{T. 'B['T]} } -->
   sequent [squash] { 'H; r: srec{T. 'B['T]} >- "type"{'S['r]} } -->
   sequent [squash] { 'H; T1: univ[i:l]; z: \subtype{'T1; srec{T. 'B['T]}};
               v: w: 'T1 -> 'S['w]; w: 'B['T1]
           >- 't1['v; 'w] = 't2['v; 'w] in 'S['w]
           } -->
   sequent ['ext] { 'H >- srecind{'r1; h1, z1. 't1['h1; 'z1]}
                   = srecind{'r2; h2, z2. 't2['h2; 'z2]}
                   in 'S['r1]
           }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_srec_term : term -> bool
val dest_srec : term -> string * term
val mk_srec_term : string -> term -> term

val is_srecind_term : term -> bool
val dest_srecind : term -> string * string * term * term
val mk_srecind_term : string -> string -> term -> term -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
