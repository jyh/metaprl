(*!
 * @begin[spelling]
 * sqSubstT sqeq
 * @end[spelling]


 * @begin[doc]
 * @theory[Itt_squiggle]
 *
 * The @tt{Itt_squiggle} module defines the squiggle equality.
 * The squiggle equality $<<'t ~ 's>>$ holds for closed terms $t$ and $s$ iff
 * $t$ can be reduced to $s$. We can expand this semantics for open terms
 * in the given context the same way as for any other type.
 * For example one can prove that
 * $$@sequent{ext; {H; x@colon @prod{A;B}}; x  ~  @pair{@fst{x};@snd{x}}}$$
 * This is a conditional rewrite: it states that we can replace $x$ with
 * $@pair{@fst{x};@snd{x}}$ only when we know that $x$ is from a product type.
 * The rules @hrefrule[squiggleSubstitution] and @hrefrule[squiggleHypSubstitution]
 * define when such substitution would be valid.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * @end[license]
 *)

(*!************************************************************************
 * @begin[doc]
 * @parents
 * @end[doc]
 *)

extends Itt_equal
extends Itt_struct
extends Itt_squash

(*! @docoff *)
extends Itt_comment

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

open Var
open Tactic_type.Sequent
open Tactic_type.Tacticals
open Tactic_type
open Tactic_type.Tacticals
open Mptop

open Base_dtactic

open Itt_equal
open Itt_struct
open Itt_squash

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_squiggle%t"


(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*************************************************************************
 * @begin[doc]
 * @terms
 * The @tt{sqeq} term defines the squiggle equality.
 *
 * @end[doc]
 *)
(*
declare "sqeq"{'t;'s}
*)

(*! @docoff *)

dform sqeq_df : ('a ~ 'b) = slot{'a} sim slot{'b}


let squiggle_term = << 'a ~ 'b >>
let squiggle_opname = opname_of_term squiggle_term
let is_squiggle_term = is_dep0_dep0_term squiggle_opname
let dest_squiggle = dest_dep0_dep0_term squiggle_opname
let mk_squiggle_term = mk_dep0_dep0_term squiggle_opname



(*!
 * @begin[doc]
   @rewrites
 * @thysubsection{Typehood and equality}
   The squiggle relation $<<'t ~ 's>>$ is a type if and only if
   it holds.  Two squiggle relation $<<'t_1 ~ 's_1>>$ and $<<'t_2 ~ 's_2>>$
   are equal as types whenever they are correct types.
 * @end[doc]
*)
prim squiggleEquality {| intro []; eqcd |} 'H :
  [wf] sequent[squash] { 'H >- 't1 ~ 's1 } -->
  [wf] sequent[squash] { 'H >- 't2 ~ 's2 } -->
  sequent['ext] { 'H >- ('t1 ~ 's1) = ('t2 ~ 's2) in univ[i:l]} =
  it

interactive squiggleFormation 'H ('t ~ 's) :
  [wf] sequent[squash] { 'H >- 't ~ 's } -->
  sequent['ext] { 'H >- univ[i:l]}
     (* = 't ~ 's *)

interactive squiggleType {| intro [] |} 'H :
  [wf] sequent[squash] { 'H >- 't ~ 's } -->
  sequent['ext] { 'H >- "type"{.'t ~ 's}}

(*!
 * @begin[doc]
 * @thysubsection{Membership}
 * The $@it$ term is the one-and-only element
 * in a provable squiggle equality type.
 * @end[doc]
 *)

prim squiggle_memberEquality {| intro []; eqcd; squash |} 'H :
  [wf] sequent[squash] { 'H >- 't ~ 's } -->
  sequent['ext] { 'H >- it IN ('t ~ 's)} =
  it

prim squiggleElimination {|  elim [ThinOption thinT] |} 'H 'J :
   ('t : sequent['ext] { 'H; x: ('t ~ 's); 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: ('t ~ 's); 'J['x] >- 'C['x] } =
   't

(*!
 * @begin[doc]
 * @thysubsection{Substitution}
 * If we can prove that $<<'t ~ 's>>$, then we can substitute $s$ for $t$
 * in any place without generating any well-formedness subgoals.
 * @end[doc]
 *)

prim squiggleSubstitution 'H ('t ~ 's) bind{x. 'A['x]} :
  [equality] sequent[squash] { 'H >- 't ~ 's } -->
  [main] ('t : sequent['ext] { 'H >- 'A['s] }) -->
   sequent ['ext] { 'H >-  'A['t] } =
   't

prim squiggleHypSubstitution 'H 'J ('t ~ 's) bind{x. 'A['x]}:
   [equality] sequent [squash] { 'H; x: 'A['t]; 'J['x] >- 't ~ 's } -->
   [main] ('t : sequent ['ext] { 'H; x: 'A['s]; 'J['x] >- 'C['x] }) -->
   sequent ['ext] { 'H; x: 'A['t]; 'J['x] >- 'C['x] } =
   't

(*!
 * @begin[doc]
 * The  @tt{sqSubstT} tactic takes a clause number $i$, and
 * a term $<<'t ~ 's>>$ and applies one of two above rules.
 * This tactic substitutes the term $s$ for
 * @emph{all} occurrences of the term $t$ in the clause.
 * One can give a term  $<< bind{x. 'A['x]} >>$ as an optional with-argument
 * to specify exact location of the subterm to be replaced.
 * @end[doc]
 *)

(*!
 * @begin[doc]
 * @thysubsection{Squiggle equality is an equivalence relation}
 * Squiggle equality is reflexive, symmetric and transitive.
 * @end[doc]
 *)


prim squiggleRef {|  intro [] |} 'H :
   sequent ['ext] { 'H >- 't ~ 't } =
   it

interactive squiggleSym 'H :
   sequent [squash] { 'H >- 's ~ 't } -->
   sequent ['ext] { 'H >- 't ~ 's }

interactive squiggleTrans 'H 'r :
   sequent [squash] { 'H >- 't ~ 'r } -->
   sequent [squash] { 'H >- 'r ~ 's } -->
   sequent ['ext] { 'H >- 't ~ 's }

(*! @docoff *)



(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(* substitution *)


let sqSubstConclT t p =
   let a, _ = dest_squiggle t in
   let bind =
      try
         let t1 = get_with_arg p in
            if is_xbind_term t1 then
               t1
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", t)))
      with
         RefineError _ ->
            let x = get_opt_var_arg "z" p in
               mk_xbind_term x (var_subst (Sequent.concl p) a x)
   in
      squiggleSubstitution (Sequent.hyp_count_addr p) t bind p

(*
 * Hyp substitution requires a replacement.
 *)
let sqSubstHypT i t p =
   let a, _ = dest_squiggle t in
   let _, t1 = Sequent.nth_hyp p i in
   let bind =
      try
         let b = get_with_arg p in
            if is_xbind_term b then
               b
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", b)))
      with
         RefineError _ ->
            let z = get_opt_var_arg "z" p in
               mk_xbind_term z (var_subst t1 a z)
   in
   let i, j = Sequent.hyp_indices p i in
      squiggleHypSubstitution i j t bind p

(*
 * General substition.
 *)
let sqSubstT t i =
   if i = 0 then
      sqSubstConclT t
   else
      sqSubstHypT i t


let sqSymT p = squiggleSym (Sequent.hyp_count_addr p) p
