
include Itt_equal
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
   show_loading "Loading Itt_pointwise%t"

(* debug_string DebugLoad "Loading itt_struct..." *)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(* The following two rules are valid only for pointwise functionality.
 * They both contradict to Let rule.
 *)

prim hypSubstPointwise 'H 'J_1 'J_2  't1  bind{y. 'A['y]} :
   [equality] sequent ['ext] { 'H; t:'T; 'J_1['t];  x: 'A['t]; 'J_2['x;'t] >- 't = 't1 in 'T } -->
   [main] ('c : sequent ['ext] { 'H; t:'T; 'J_1['t];  x: 'A['t1]; 'J_2['x;'t] >- 'C['x;'t] }) -->
   sequent ['ext] { 'H; t:'T; 'J_1['t];  x: 'A['t]; 'J_2['x;'t] >- 'C['x;'t] } =
   'c

prim contextSubstPointwise 'H 'J_1 'J 'J_2 't1  :
   [equality] sequent ['ext] { 'H; t:'T; 'J_1['t];  'J['t]; 'J_2['t] >- 't = 't1 in 'T } -->
   [main] ('c : sequent ['ext] { 'H; t:'T; 'J_1['t];  'J['t1]; 'J_2['t] >- 'C['t] }) -->
   sequent ['ext] { 'H; t:'T; 'J_1['t];  'J['t]; 'J_2['t] >- 'C['t] } =
   'c
