include Itt_equal
include Itt_struct

(*! @docoff *)

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


let squiggle_term = << 'a ~ 'b >>
let squiggle_opname = opname_of_term squiggle_term
let is_squiggle_term = is_dep0_dep0_term squiggle_opname
let dest_squiggle = dest_dep0_dep0_term squiggle_opname
let mk_squiggle_term = mk_dep0_dep0_term squiggle_opname



prim squiggleEquality {| intro_resource []; eqcd_resource |} 'H :
  [wf] sequent[squash] { 'H >- 't1 ~ 's1 } -->
  [wf] sequent[squash] { 'H >- 't2 ~ 's2 } -->
  sequent['ext] { 'H >- ('t1 ~ 's1) = ('t2 ~ 's2) in univ[i:l]} =
  it

interactive squiggleFormation 'H ('t ~ 's) :
  [wf] sequent[squash] { 'H >- 't ~ 's } -->
  sequent['ext] { 'H >- univ[i:l]}
     (* = 't ~ 's *)

interactive squiggleType {| intro_resource [] |} 'H :
  [wf] sequent[squash] { 'H >- 't ~ 's } -->
  sequent['ext] { 'H >- "type"{.'t ~ 's}}

prim squiggle_memberEquality {| intro_resource []; eqcd_resource |} 'H :
  [wf] sequent[squash] { 'H >- 't ~ 's } -->
  sequent['ext] { 'H >- it IN ('t ~ 's)} =
  it

prim squiggleElimination {|  elim_resource [ThinOption thinT] |} 'H 'J :
   ('t : sequent['ext] { 'H; x: ('t ~ 's); 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: ('t ~ 's); 'J['x] >- 'C['x] } =
   't

prim squiggleSubstitution 'H ('t ~ 's) bind{x. 'C['x]} :
  ["rewrite"] sequent[squash] { 'H >- 't ~ 's } -->
  [main] ('t : sequent['ext] { 'H >- 'C['s] }) -->
   sequent ['ext] { 'H >-  'C['t] } =
   't

prim squiggleHypSubstitution 'H 'J ('t ~ 's) bind{x. 'A['x]}:
   ["rewrite"] sequent [squash] { 'H; x: 'A['t]; 'J['x] >- 't ~ 's } -->
   [main] ('t : sequent ['ext] { 'H; x: 'A['s]; 'J['x] >- 'C['x] }) -->
   sequent ['ext] { 'H; x: 'A['t]; 'J['x] >- 'C['x] } =
   't



prim squiggleRef {|  intro_resource [] |} 'H :
   sequent ['ext] { 'H >- 't ~ 't } =
   it

interactive squiggleSym 'H :
   sequent [squash] { 'H >- 's ~ 't } -->
   sequent ['ext] { 'H >- 't ~ 's }

interactive squiggleTrans 'H 'r :
   sequent [squash] { 'H >- 't ~ 'r } -->
   sequent [squash] { 'H >- 'r ~ 's } -->
   sequent ['ext] { 'H >- 't ~ 's }


let sqSubstConclT t p =
   let a, _ = dest_squiggle t in
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
            if is_bind_term b then
               b
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", b)))
      with
         RefineError _ ->
            let z = get_opt_var_arg "z" p in
               mk_bind_term z (var_subst t1 a z)
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
