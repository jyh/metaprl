(*
 * PArameterized recursive type.
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
include Itt_subtype
include Itt_void
include Itt_fun
include Itt_prod

open Printf
open Mp_debug
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Mp_resource

open Itt_void

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_prec%t" eflush

(* debug_string DebugLoad "Loading itt_prec..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Parameterized recursive type has an additional
 * argument x, with initial value a.
 *)
declare "prec"{T, x. 'B['T; 'x]; 'a}
declare precind{'a; p, h. 'g['p; 'h]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw reducePrecind : precind{'a; p, h. 'g['p; 'h]} <-->
   'g[lambda{a. precind{'a; p, h. 'g['p; 'h]}}; 'a]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- prec(A1, x1. B1[A1; x1]; a1) = prec(A2, x2. B2[A2; x2]; a2) in Ui
 * by precEquality A x y z T P1 P2
 *
 * H >- a1 = a2 in A
 * H; x: A; T: A -> Ui >- B1[T; x] = B2[T; x] in Ui
 * H; P1: A -> Ui; P2: A -> Ui; z: x:A -> y: P1 x -> (y in P2 x); x:A; y: B1[P1; x]
 *   >- y = y in B2[P2; x]
 *)
prim precEquality 'H 'A 'x 'y 'z 'T 'P1 'P2 :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H; x: 'A; T: 'A -> univ[@i:l] >- 'B1['T; 'x] = 'B2['T; 'x] in univ[@i:l] } -->
   sequent [squash] { 'H;
             P1: 'A -> univ[@i:l];
             P2: 'A -> univ[@i:l];
             z: x:'A -> subtype{('P1 'x); ('P2 'x)};
             x: 'A;
             y: 'B1['P1; 'x]
           >- 'y = 'y in 'B1['P2; 'x]
           } -->
   sequent ['ext] { 'H >- "prec"{A1, x1. 'B1['A1; 'x1]; 'a1}
                   = "prec"{A2, x2. 'B2['A2; 'x2]; 'a2}
                   in univ[@i:l]
           } =
   it

(*
 * H >- prec(T, x. B[T; x]; a) ext t
 * by precMemberFormation
 *
 * H >- B[lambda(a. prec(T, x. B[T; x])); a] ext t
 * H >- prec(T, x. B[T; x]; a) = prec(T, x. B[T; x]; a) in type
 *)
prim precMemberFormation 'H :
   ('t : sequent ['ext] { 'H >- 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a] }) -->
   sequent [squash] { 'H >- "type"{("prec"{T, x. 'B['T; 'x]; 'a})} } -->
   sequent ['ext] { 'H >- "prec"{T, x. 'B['T; 'x]; 'a} } =
   't

(*
 * H >- a1 = a2 in prec(T, x. B[T; x]. a)
 * by precMemberEquality
 *
 * H >- prec(T, x. B[T; x]. a) = prec(T, x. B[T; x]. a) in type
 * H >- a1 = a2 in B[lambda(a. prec(T, x. B[T; x]); a); a]
 *)
prim precMemberEquality 'H 'z :
   sequent [squash] { 'H >- "type"{("prec"{T, x. 'B['T; 'x]; 'a})} } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a] } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in "prec"{T, x. 'B['T; 'x]; 'a} } =
   it

(*
 * H; r: prec(T, x. B[T; x]; a); J[r] >- T[a] ext precind(a; p, h. g[r, lambda(x. it), h, p]
 * by precElimination lambda(z. T[z]) A Z u h y
 *
 * H; r: prec(T, x. B[T; x]; a); J[r] >- a = a in A
 * H; r: prec(T, x. B[T; x]; a); J[r]; Z: A -> Ui
 *   u: p: (a: A * Z a) -> (p = p in a: A * prec(T, x. B[T; x]; a);
 *   h: p: (a: A * Z a) -> G[p];
 *   p: a: A * B[Z, a]
 * >- T[p] ext g[r, u, h, p]
 *)
prim precElimination 'H 'J lambda{z. 'G['z]} 'a 'A 'Z 'r 'p 'u 'h univ[@i:l] :
   sequent [squash] { 'H; r: "prec"{T, x. 'B['T; 'x]; 'a}; 'J['r] >- 'a = 'a in 'A } -->
   ('g['r; 'u; 'p; 'h] : sequent ['ext] { 'H; r: "prec"{T, x. 'B['T; 'x]; 'a}; 'J['r];
      Z: 'A -> univ[@i:l];
      u: subtype{(a: 'A * 'Z 'a); (a: 'A * "prec"{T, x. 'B['T; 'x]; 'a})};
      h: p: (a: 'A * 'Z 'a) -> 'G['p];
      p: a: 'A * 'B['Z; 'a]
   >- 'G['p]
   }) -->
   sequent ['ext] { 'H; r: "prec"{T, x. 'B['T; 'x]; 'a}; 'J['r] >- 'G['a] } =
   precind{'a; p, h. 'g['r; lambda{x. it}; 'p; 'h]}

(*
 * H; r: prec(T, x. B[T; x]; a); J[r] >- T[r]
 * by precUnrollElimination y u
 *
 * H; r: prec(T, x. B[T; x]; a); J[r];
 *   y: B[lambda(a. prec(T, x. B[T; x]); a); a];
 *   u: r = y in B[lambda(a. prec(T, x. B[T; x]); a); a]
 *   >- T[y]
 *)
prim precUnrollElimination 'H 'J 'z 'y 'u :
   ('g['z; 'y; 'u] : sequent ['ext] { 'H; r: "prec"{T, x. 'B['T; 'x]; 'a}; 'J['r];
             y: 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a];
             u: 'r = 'y in 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a]
             >- 'G['y]
           }) -->
   sequent ['ext] { 'H; r: "prec"{T, x. 'B['T; 'x]; 'a}; 'J['r] >- 'G['r] } =
   'g['z; 'z; it]

(*
 * H >- precind(r1; h1, z1. t1[r1, z1]) = precind(r2; h2, z2. t2[r2; z2]) in S[r1]
 * by precindEquality lambda(x. S[x]) (a:A * prec(T, y. B[T; y]; a)) Z u h z
 *
 * H >- r1 = r2 in a:A * prec(T, y. B[T, y]; a)
 * H; Z: A -> Ui;
 *   u: z: (a:A * Z a) -> (z = z in a:A * prec(T, x. B[t, x]; a));
 *   h: z: (a:A * Z a) -> S[z];
 *   z: a: A * B[Z; a]
 *   >- t1[h; z] = t2[h; z] in S[z]
 *)
prim precindEquality 'H lambda{x. 'S['x]} (a:'A * "prec"{T, y. 'B['T; 'y]; 'a}) 'Z 'u 'h 'z univ[@i:l] :
   sequent [squash] { 'H >- 'r1 = 'r2 in a: 'A * "prec"{T, y. 'B['T; 'y]; 'a} } -->
   sequent [squash] { 'H; Z: 'A -> univ[@i:l];
             u: subtype{(a: 'A * 'Z 'a); (a: 'A * "prec"{T, x. 'B['T; 'x]; 'a})};
             h: z: (a: 'A * 'Z 'a) -> 'S['z];
             z: a: 'A * 'B['Z; 'a]
             >- 't1['h; 'z] = 't2['h; 'z] in 'S['z]
           } -->
   sequent ['ext] { 'H >- precind{'r1; h1, z1. 't1['h1; 'z1]}
                   = precind{'r2; h2, z2. 't2['h2; 'z2]}
                   in 'S['r1]
           } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let prec_term = << "prec"{T, x. 'B['T; 'x]; 'a} >>
let prec_opname = opname_of_term prec_term
let is_prec_term = is_dep2_dep0_term prec_opname
let dest_prec = dest_dep2_dep0_term prec_opname
let mk_prec_term = mk_dep2_dep0_term prec_opname

let precind_term = << precind{'a; p, h. 'g['p; 'h]} >>
let precind_opname = opname_of_term precind_term
let is_precind_term = is_dep0_dep2_term precind_opname
let dest_precind = dest_dep0_dep2_term precind_opname
let mk_precind_term = mk_dep0_dep2_term precind_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of prec.
 *)
let inf_prec f decl t =
   let a, b, body, arg = dest_prec t in
   let decl', arg' = f decl arg in
      f (add_unify_subst a void_term (add_unify_subst b arg' decl')) body

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (prec_term, inf_prec)

(*
 * Type of precind.
 * WRONG!
 *)
let inf_precind f decl t =
   let p, h, a, g = dest_precind t in
   let decl', a' = f decl a in
      f (add_unify_subst p a' (add_unify_subst h a' decl')) g

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (precind_term, inf_precind)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
