(*
 * Strutural rules.
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

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Var
open Mptop

open Base_auto_tactic

open Itt_equal

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_struct%t"

(* debug_string DebugLoad "Loading itt_struct..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * This is just syntax for a binding term.
 * It has no semantic meaning in the type theory.
 *)
declare bind{x. 'T['x]}

let bind_term = << bind{x. 'T['x]} >>
let bind_opname = opname_of_term bind_term
let is_bind_term = is_dep1_term bind_opname
let dest_bind = dest_dep1_term bind_opname
let mk_bind_term = mk_dep1_term bind_opname

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H; x: A; J >- A ext x
 * by hypothesis
 *)
prim hypothesis 'H 'J 'x :
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'A } =
   'x

(*
 * H, x: A, J >- A ext t
 * by thin
 * H, J >- A ext t
 *)
prim thin 'H 'J : 
   ('t : sequent ['ext] { 'H; 'J >- 'C }) -->
   sequent ['ext] { 'H; x: 'A; 'J >- 'C } =
   't


(*
 * H, J >- T ext t[s]
 * by cut S
 * H, J >- S ext s
 * H, x: S, J >- T ext t[x]
 *)
prim cut 'H 'J 'S 'x :
   [assertion] ('a : sequent ['ext] { 'H; 'J >- 'S }) -->
   [main] ('f['x] : sequent ['ext] { 'H; x: 'S; 'J >- 'T }) -->
   sequent ['ext] { 'H; 'J >- 'T } =
   'f['a]

(*
 * This is usually used for performance testing.
 *)
interactive dup 'H :
   sequent ['ext] { 'H >- 'T } -->
   sequent ['ext] { 'H >- 'T } -->
   sequent ['ext] { 'H >- 'T}

(*
 * H >- T
 * by introduction t
 * H >- t = t in T
 *)
prim introduction 'H 't :
   [wf] sequent [squash] { 'H >- member{'T; 't} } -->
   sequent ['ext] { 'H >- 'T } =
   't

(*
 * H >- T1[t1] ext t
 * by substitution (t1 = t2 in T2) lambda(x. T1[x])
 * H >- t1 = t2 in T2
 * H >- T1[t2] ext t
 * H, x: T2 >- T1[x] = T1[x] in type
 *)
prim substitution 'H ('t1 = 't2 in 'T2) bind{x. 'T1['x]} :
   [equality] sequent [squash] { 'H >- 't1 = 't2 in 'T2 } -->
   [main] ('t : sequent ['ext] { 'H >- 'T1['t2] }) -->
   [wf] sequent [squash] { 'H; x: 'T2 >- "type"{'T1['x]} } -->
   sequent ['ext] { 'H >- 'T1['t1] } =
   't

(*
 * H, x: A, J >- T ext t
 * by hypothesesReplacement B
 * H, x:B, J >- T ext t
 * H, x: A, J >- A = B in type
 *)
prim hypReplacement 'H 'J 'B univ[i:l] :
   [main] ('t : sequent ['ext] { 'H; x: 'B; 'J['x] >- 'T['x] }) -->
   [equality] sequent [squash] { 'H; x: 'A; 'J['x] >- 'A = 'B in univ[i:l] } -->
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'T['x] } =
   't

(*
 * H; x: A[t1]; J[x] >> T1[x] ext t
 * by hypSubstitution (t1 = t2 in T2) bind(x. A[x])
 * H; x: A[t1]; J[x] >> t1 = t2 in T2
 * H; x: A[t2]; J[x] >> T1[x]
 * H, x: A[t1]; J[x]; z: T2 >> A[z] in type
 *)
prim hypSubstitution 'H 'J ('t1 = 't2 in 'T2) bind{y. 'A['y]} 'z :
   [equality] sequent [squash] { 'H; x: 'A['t1]; 'J['x] >- 't1 = 't2 in 'T2 } -->
   [main] ('t : sequent ['ext] { 'H; x: 'A['t2]; 'J['x] >- 'T1['x] }) -->
   [wf] sequent [squash] { 'H; x: 'A['t1]; 'J['x]; z: 'T2 >- "type"{'A['z]} } -->
   sequent ['ext] { 'H; x: 'A['t1]; 'J['x] >- 'T1['x] } =
   't

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Prove by hypothesis.
 *)
let nthHypT i p =
   let x, h = Sequent.nth_hyp p i in
   let i, j = Sequent.hyp_indices p i in
      hypothesis i j x p

(*
 * Thin a hyp.
 * Check that this doesn't introduce a free variable
 * (although the rule is still valid otherwise).
 *)
let thinT i p =
   let i, j = Sequent.hyp_indices p i in
      thin i j p

let thinAllT i j p =
   let rec tac j =
      if j < i then
         idT
      else
         thinT j thenT tac (pred j)
   in
      tac j p

(*
 * Cut rule.
 *)
let assertT s p =
   let j, k = Sequent.hyp_split_addr p (Sequent.hyp_count p) in
   let v = maybe_new_vars1 p "v" in
      cut j k s v p

(*
 * Cut in at a certain point.
 *)
let assertAtT i s p =
   let i, j = Sequent.hyp_split_addr p i in
   let v = get_opt_var_arg "v" p in
      cut i j s v p

let dupT p =
   dup (Sequent.hyp_count_addr p) p

(*
 * Explicit extract.
 *)
let useWitnessT t p =
   introduction (Sequent.hyp_count_addr p) t p

(*
 * Substitution.
 * The binding term may be optionally supplied.
 *)
let substConclT t p =
   let _, a, _ = dest_equal t in
   let bind =
      try
         let t1 = get_with_arg p in
            if is_bind_term t1 then
               t1
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", t)))
      with
         RefineError _ ->
            let x = get_opt_var_arg "z" p in
               mk_bind_term x (var_subst (Sequent.concl p) a x)
   in
      substitution (Sequent.hyp_count_addr p) t bind p

(*
 * Hyp substitution requires a replacement.
 *)
let substHypT i t p =
   let _, a, _ = dest_equal t in
   let _, t1 = Sequent.nth_hyp p i in
   let z = get_opt_var_arg "z" p in
   let bind =
      try
         let b = get_with_arg p in
            if is_bind_term b then
               b
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", b)))
      with
         RefineError _ ->
            mk_bind_term z (var_subst t1 a z)
   in
   let i, j = Sequent.hyp_indices p i in
      hypSubstitution i j t bind z p

(*
 * General substition.
 *)
let substT t i =
   if i = 0 then
      substConclT t
   else
      substHypT i t

(*
 * Derived versions.
 *)
let hypSubstT i j p =
   let _, h = Sequent.nth_hyp p i in
      (substT h j thenET nthHypT i) p

let revHypSubstT i j p =
   let t, a, b = dest_equal (snd (Sequent.nth_hyp p i)) in
   let h' = mk_equal_term t b a in
      (substT h' j thenET (equalSymT thenT nthHypT i)) p

(*
 * Replace the entire hypothesis.
 *)
let replaceHypT t i p =
   let j, k = Sequent.hyp_indices p i in
   let univ = get_univ_arg p in
      hypReplacement j k t univ p

(*
 * Add to trivialT tactic.
 *)
let trivial_resource =
   Mp_resource.improve trivial_resource (**)
      { auto_name = "nthHypT";
        auto_prec = trivial_prec;
        auto_tac = onSomeHypT nthHypT
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
