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

include Itt_equal
include Itt_prec
include Itt_subtype
include Itt_void
include Itt_struct

open Printf
open Mp_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type.Tacticals
open Var

open Base_dtactic

open Itt_void
open Itt_equal
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_srec%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare srec{T. 'B['T]}
declare srecind{'a; p, h. 'g['p; 'h]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform srec_df : srec{T. 'B} =
   szone mu `"{" slot{'T} `"." pushm[0] slot{'B} `"}" popm ezone

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_srecind : srecind{'a; p, h. 'g['p; 'h]} <-->
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
prim srecFormation 'H 'T :
   ('B['T] : sequent ['ext] { 'H; T: univ[i:l] >- univ[i:l] }) -->
   sequent ['ext] { 'H >- univ[i:l] } =
   srec{T. 'B['T]}

(*
 * H >- srec(T1. B1[T1]) = srec(T2. B2[T2]) in Ui
 * by srecEquality T S1 S2 z
 *
 * H; T: Ui >- B1[T] = B2[T] in Ui
 * H; S1: Ui; S2: Ui; z: subtype(S1; S2) >- subtype(B1[S1]; B1[S2])
 *)
prim srecEquality {| intro_resource []; eqcd_resource |} 'H 'T 'S1 'S2 'z :
   [wf] sequent [squash] { 'H; T: univ[i:l] >- 'B1['T] = 'B2['T] in univ[i:l] } -->
   [wf] sequent [squash] { 'H; S1: univ[i:l]; S2: univ[i:l]; z: subtype{'S1; 'S2} >- subtype{'B1['S1]; 'B1['S2]} } -->
   sequent ['ext] { 'H >- srec{T1. 'B1['T1]} = srec{T2. 'B2['T2]} in univ[i:l] } =
   it

prim srecType {| intro_resource [] |} 'H 'S1 'S2 'z univ[i:l] :
   [wf] sequent [squash] { 'H; S1: univ[i:l]; S2: univ[i:l]; z: subtype{'S1; 'S2} >- subtype{'B['S1]; 'B['S2]} } -->
   sequent ['ext] { 'H >- "type"{srec{T. 'B['T]}} } =
   it

(*
 * H >- srec(T. B[T]) ext g
 * by srec_memberFormation
 *
 * H >- B[srec(T. B[T])] ext g
 * H >- srec(T. B[T]) = srec(T. B[T]) in Ui
 *)
prim srec_memberFormation {| intro_resource [] |} 'H :
   [wf] ('g : sequent ['ext] { 'H >- 'B[srec{T. 'B['T]}] }) -->
   [wf] sequent [squash] { 'H >- "type"{(srec{T. 'B['T]})} } -->
   sequent ['ext] { 'H >- srec{T. 'B['T]} } =
   'g

(*
 * H >- x1 = x2 in srec(T. B[T])
 * by srec_memberEquality
 *
 * H >- x1 = x2 in B[srec(T. B[T])]
 * H >- srec(T. B[T]) = srec(T. B[T]) in Ui
 *)
prim srec_memberEquality {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- 'x1 = 'x2 in 'B[srec{T. 'B['T]}] } -->
   [wf] sequent [squash] { 'H >- "type"{(srec{T. 'B['T]})} } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in srec{T. 'B['T]} } =
   it

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
prim srecElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'x srec{T. 'B['T]} 'T1 'u 'v 'w 'z univ[i:l] :
   [main] ('g['x; 'T1; 'u; 'w; 'z] : sequent ['ext] {
             'H;
             x: srec{T. 'B['T]};
             'J['x];
             T1: univ[i:l];
             u: subtype{'T1; srec{T. 'B['T]}};
             w: v: 'T1 -> 'C['v];
             z: 'B['T1]
           >- 'C['z]
           }) -->
   sequent ['ext] { 'H; x: srec{T. 'B['T]}; 'J['x] >- 'C['x] } =
   srecind{'x; p, h. 'g['x; srec{T. 'B['T]}; it; 'p; 'h]}

(*
 * H, x: srec(T. B[T]); J[x] >- C[x]
 * by srecUnrollElimination y u
 *
 * H, x: srec(T. B[T]); J[x]; y: B[srec(T. B[T])]; u: x = y in B[srec(T. B[T])] >- C[y]
 *)
prim srecUnrollElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'x 'y 'u :
   [main] ('g['x; 'y; 'u] : sequent ['ext] { 'H; x: srec{T. 'B['T]}; 'J['x]; y: 'B[srec{T. 'B['T]}]; u: 'x = 'y in 'B[srec{T. 'B['T]}] >- 'C['y] }) -->
   sequent ['ext] { 'H; x: srec{T. 'B['T]}; 'J['x] >- 'C['x] } =
   'g['x; 'x; it]

(*
 * H >- srecind(r1; h1, z1. t1) = srecind(r2; h2, z2. t2) in S[r1]
 * by srecindEquality lambda(x. S[x]) srec(T. B[T]) T1 u v w z
 *
 * H >- r1 = r2 in srec(T. B[T])
 * H, T1: Ui, z: subtype(T1; srec(T. B[T])),
 *    v: w: T1 -> S[w], w: T[T1]
 *    >- t1[v; w] = t2[v; w] in S[w]
 *)
prim srecindEquality {| intro_resource []; eqcd_resource |} 'H lambda{x. 'S['x]} srec{T. 'B['T]} 'T1 'u 'v 'w 'z univ[i:l] :
   [wf] sequent [squash] { 'H >- 'r1 = 'r2 in srec{T. 'B['T]} } -->
   [wf] sequent [squash] { 'H; T1: univ[i:l]; z: subtype{'T1; srec{T. 'B['T]}};
               v: w: 'T1 -> 'S['w]; w: 'B['T1]
           >- 't1['v; 'w] = 't2['v; 'w] in 'S['w]
           } -->
   sequent ['ext] { 'H >- srecind{'r1; h1, z1. 't1['h1; 'z1]}
                   = srecind{'r2; h2, z2. 't2['h2; 'z2]}
                   in 'S['r1]
           } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let srec_term = << srec{T. 'B['T]} >>
let srec_opname = opname_of_term srec_term
let is_srec_term = is_dep1_term srec_opname
let dest_srec = dest_dep1_term srec_opname
let mk_srec_term = mk_dep1_term srec_opname

let srecind_term = << srecind{'a; p, h. 'g['p; 'h]} >>
let srecind_opname = opname_of_term srecind_term
let is_srecind_term = is_dep0_dep2_term srecind_opname
let dest_srecind = dest_dep0_dep2_term srecind_opname
let mk_srecind_term = mk_dep0_dep2_term srecind_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of srec.
 *)
let inf_srec f decl t =
   let a, body = dest_srec t in
      f (add_unify_subst a void_term decl) body

let typeinf_resource = Mp_resource.improve typeinf_resource (srec_term, inf_srec)

(*
 * Type of srecind.
 * WRONG.
 *)
let inf_srecind f decl t =
   let p, h, a, g = dest_srecind t in
   let decl', a' = f decl a in
      f (add_unify_subst p a' (add_unify_subst h a' decl')) g

let typeinf_resource = Mp_resource.improve typeinf_resource (srecind_term, inf_srecind)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
