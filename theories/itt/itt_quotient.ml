(*
 * Quotient type.
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
include Itt_set
include Itt_rfun
include Itt_struct

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type.Sequent
open Tactic_type.Tacticals

open Base_dtactic

open Itt_equal
open Itt_subtype
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_quotient%t" eflush

(* debug_string DebugLoad "Loading itt_quotient..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "quot"{'A; x, y. 'E['x; 'y]}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_quot

dform quot_df1 : parens :: "prec"[prec_quot] :: "quot"{'A; x, y. 'E} =
   slot{'x} `", " slot{'y} `":" " " slot{'A} `" // " slot{'E}

dform quot_df2 : mode[src] :: parens :: "prec"[prec_quot] :: "quot"{'A; x, y. 'E} =
   `"quot " slot{'x} `", " slot{'y} `":" slot{'A} `" // " slot{'E}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext quot x, y: A // E
 * by quotientFormation (quot x, y: A // E) z u v
 *
 * H >- A = A in Ui
 * H, x: A, y: A >- E[x, y] = E[x, y] in Ui
 * H, x: A >- E[x, x]
 * H, x: A, y: A, u: E[x, y] >- E[y, x]
 * H, x: A, y: A, z: A, u: E[x, y], v: E[y, z] >- E[x, z]
 *)
prim quotientFormation 'H (quot x, y: 'A // 'E['x; 'y]) 'z 'u 'v :
   [wf] sequent [squash] { 'H >- 'A = 'A in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'A; y: 'A >- 'E['x; 'y] = 'E['x; 'y] in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'A >- 'E['x; 'x] } -->
   [wf] sequent [squash] { 'H; x: 'A; y: 'A; u: 'E['x; 'y] >- 'E['y; 'x] } -->
   [wf] sequent [squash] { 'H; x: 'A; y: 'A; z: 'A; u: 'E['x; 'y]; v: 'E['y; 'z] >- 'E['x; 'z] } -->
   sequent ['ext] { 'H >- univ[i:l] } =
   quot x, y: 'A // 'E['x; 'y]

(*
 * H >- quot x1, y1: A1 // E1 = quot x2, y2. A2 // E2 in Ui
 * by quotientWeakEquality x y z u v
 *
 * H >- A1 = A2 in Ui
 * H, x: A1, y: A1 >- E1[x, y] = E2[x, y] in Ui
 * H, x: A1 >- E1[x, x]
 * H, x: A1, y: A1, u: E1[x, y] >- E1[y, x]
 * H, x: A1, y: A1, z: A1, u: E1[x, y], v: E1[y, z] >- E1[x, z]
 *)
prim quotientWeakEquality {| intro_resource []; eqcd_resource |} 'H 'x 'y 'z 'u 'v :
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'A1; y: 'A1 >- 'E1['x; 'y] = 'E2['x; 'y] in univ[i:l] } -->
   [wf] sequent [squash] { 'H; x: 'A1 >- 'E1['x; 'x] } -->
   [wf] sequent [squash] { 'H; x: 'A1; y: 'A1; u: 'E1['x; 'y] >- 'E1['y; 'x] } -->
   [wf] sequent [squash] { 'H; x: 'A1; y: 'A1; z: 'A1; u: 'E1['x; 'y]; v: 'E1['y; 'z] >- 'E1['x; 'z] } -->
   sequent ['ext] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1]
                   = quot x2, y2: 'A2 // 'E2['x2; 'y2]
                   in univ[i:l]
           } =
   it

(*
 * H >- quot x1, y1: A1 // E1 = quot x2, y2. A2 // E2 in Ui
 * by quotientEquality r s v
 *
 * H >- quot x1, y1: A1 // E1 = quot x1, y1: A1 // E1 in Ui
 * H >- quot x2, y2. A2 // E2 = quot x2, y2. A2 // E2 in Ui
 * H >- A1 = A2 in Ui
 * H; v: A1 = A2 in Ui; r: A1; s: A1 >- E1[r, s] -> E2[r, s]
 * H; v: A1 = A2 in Ui; r: A1; s: A1 >- E2[r, s] -> E1[r, s]
 *)
prim quotientEquality {| intro_resource []; eqcd_resource |} 'H 'r 's 'v :
   [wf] sequent [squash] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1] = quot x1, y1: 'A1 // 'E1['x1; 'y1] in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- quot x2, y2: 'A2 // 'E2['x2; 'y2] = quot x2, y2: 'A2 // 'E2['x2; 'y2] in univ[i:l] } -->
   [wf] sequent [squash] { 'H >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent [squash] { 'H; v: 'A1 = 'A2 in univ[i:l]; r: 'A1; s: 'A1 >- 'E1['r; 's] -> 'E2['r; 's] } -->
   [wf] sequent [squash] { 'H; v: 'A1 = 'A2 in univ[i:l]; r: 'A1; s: 'A1 >- 'E2['r; 's] -> 'E1['r; 's] } -->
   sequent ['ext] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1] = quot x2, y2: 'A2 // 'E2['x2; 'y2] in univ[i:l] } =
   it

(*
 * Typehood.
 *)
prim quotientType {| intro_resource [] |} 'H 'u 'v 'w 'x1 'x2 :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; u: 'A; v: 'A >- "type"{'E['u; 'v]} } -->
   [wf] sequent [squash] { 'H; u: 'A >- 'E['u; 'u] } -->
   [wf] sequent [squash] { 'H; u: 'A; v: 'A; x1: 'E['u; 'v] >- 'E['v; 'u] } -->
   [wf] sequent [squash] { 'H; u: 'A; v: 'A; w: 'A; x1: 'E['u; 'v]; x2: 'E['v; 'w] >- 'E['u; 'w] } -->
   sequent ['ext] { 'H >- "type"{.quot x, y: 'A // 'E['x; 'y]} } =
   it

(*
 * H >- quot x, y: A // E ext a
 * by quotient_memberFormation
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- A ext a
 *)
prim quotient_memberFormation {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   [main] ('a : sequent ['ext] { 'H >- 'A }) -->
   sequent ['ext] { 'H >- quot x, y: 'A // 'E['x; 'y] } =
   'a

(*
 * H >- a1 = a2 in quot x, y: A // E
 * by quotient_memberWeakEquality
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- x1 = a2 in A
 *)
prim quotient_memberWeakEquality {| intro_resource [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   [wf] sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] } =
   it

(*
 * H >- a1 = a2 in quot x, y: A // E
 * by quotient_memberEquality
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- a1 = a1 in A
 * H >- a2 = a2 in A
 * H >- E[a1; a2]
 *)
prim quotient_memberEquality {| intro_resource []; eqcd_resource |} 'H :
   [wf] sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'a1} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'a2} } -->
   [wf] sequent [squash] { 'H >- 'E['a1; 'a2] } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] } =
   it

(*
 * Membership.
 *)
prim quotientMember {| intro_resource [] |}  'H :
   [wf] sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'l} } -->
   sequent ['ext] { 'H >- member{(quot x, y: 'A // 'E['x; 'y]); 'l} } =
   it

(*
 * H, a: quot x, y: A // E, J[x] >- s[a] = t[a] in T[a]
 * by quotientElimination v w z
 *
 * H, a: quot x, y: A // E, J[x] >- T[a] = T[a] in Ui
 * H, a: quot x, y: A // E, J[x], v: A, w: A, z: E[v, w] >- s[v] = t[w] in T[v]
 *)
prim quotientElimination1 {| elim_resource [ThinOption thinT] |} 'H 'J 'v 'w 'z :
   [wf] sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- "type"{'T['a]} } -->
   [main] sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a];
             v: 'A; w: 'A; z: 'E['v; 'w] >- 's['v] = 't['w] in 'T['v]
           } -->
   sequent ['ext] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- 's['a] = 't['a] in 'T['a] } =
   it

prim quotientElimination2 {| elim_resource [ThinOption thinT] |} 'H 'J 'v 'w 'z :
   [wf] sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- "type"{'T['a]} } -->
   [main] sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y];
             v: 'A; w: 'A; z: 'E['v; 'w]; 'J['v] >- 's['v] = 't['w] in 'T['v]
           } -->
   sequent ['ext] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- 's['a] = 't['a] in 'T['a] } =
   it

(*
 * H, x: a1 = a2 in quot x, y: A // E, J[x] >- T[x]
 * by quotient_equalityElimination v
 *
 * H, x: a1 = a2 in quot x, y: A // E, J[x], v: hide(E[a, b]) >- T[x]
 *)
prim quotient_equalityElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'v :
   [main] ('g['v] : sequent ['ext] { 'H; x: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; 'J['x]; v: hide('E['a1; 'a2]) >- 'T['x] }) -->
   sequent ['ext] { 'H; x: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; 'J['x] >- 'T['x] } =
   'g[it]

(*
 * Elimination under membership.
 *)
prim quotient_memberElimination {| elim_resource [ThinOption thinT] |} 'H 'J 'v 'w 'z :
   [wf] sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- "type"{'T['a]} } -->
   [main] sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y];
             v: 'A; w: 'A; z: 'E['v; 'w]; 'J['v] >- 's['v] = 's['w] in 'T['v]
           } -->
   sequent ['ext] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- member{'T['a]; 's['a]} } =
   it

(*
 * H >- quot x1, y1: A1 // E1[x1; y1] <= quot x2, y2: A2 // E2[x2; y2]
 * by quotientSubtype
 *
 * H >- A1 <= A2
 * H, x1: A1, y1: A1 >- E1[x1; y1] => E2[x2; y2]
 * H >- quot x1, y1: A1 // E1[x1; y1] in type
 * H >- quot x2, y2: A2 // E2[x2; y2] in type
 *)
prim quotientSubtype 'H 'a1 'a2 :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H; a1: 'A1; a2: 'A1 (* ; 'E1['a1; 'a2] *) >- 'E2['a1; 'a2] } -->
   sequent [squash] { 'H >- "type"{(quot x1, y1: 'A1 // 'E1['x1; 'y1])} } -->
   sequent [squash] { 'H >- "type"{(quot x2, y2: 'A2 // 'E2['x2; 'y2])} } -->
   sequent ['ext] { 'H >- subtype{ (quot x1, y1: 'A1 // 'E1['x1; 'y1]); (quot x2, y2: 'A2 // 'E2['x2; 'y2]) } } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let quotient_term = << "quot"{'A; x, y. 'E['x; 'y]} >>
let quotient_opname = opname_of_term quotient_term
let is_quotient_term = is_dep0_dep2_term quotient_opname
let dest_quotient = dest_dep0_dep2_term quotient_opname
let mk_quotient_term = mk_dep0_dep2_term quotient_opname

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of quotient.
 *)
let inf_quotient f decl t =
   let x, y, a, e = dest_quotient t in
   let decl', a' = f decl a in
   let decl'', e' = f (add_unify_subst x a (add_unify_subst y a decl')) e in
   let le1, le2 = dest_univ a', dest_univ e' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2 0)

let typeinf_resource = Mp_resource.improve typeinf_resource (quotient_term, inf_quotient)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two quotient types.
 *)
let quotient_subtypeT p =
   (match maybe_new_vars ["x"; "y"] (declared_vars p) with
       [x; y] ->
          (quotientSubtype (hyp_count_addr p) x y
           thenLT [addHiddenLabelT "subtype";
                   addHiddenLabelT "aux";
                   addHiddenLabelT "wf";
                   addHiddenLabelT "wf"])

     | _ -> failT) p

let sub_resource =
   Mp_resource.improve
   sub_resource
   (DSubtype ([<< quot x1, y1: 'A1 // 'E1['x1; 'y1] >>, << quot x2, y2: 'A2 // 'E2['x2; 'y2] >>;
               << 'A1 >>, << 'A2 >>],
              quotient_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
