doc <:doc< 
   @begin[doc]
   @module[Itt_pointwise]
   @parents
   @end[doc]
>>

extends Itt_equal
doc <:doc< @docoff >>

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
let _ = show_loading "Loading Itt_pointwise%t"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rules
   The following two rules are valid only for pointwise functionality.
   They both contradict to @hrefrule[Let] rule.
   @end[doc]
>>

prim hypSubstPointwise 'H 'J_1 't1  bind{y. 'A['y]} :
   [equality] sequent ['ext] { 'H; t:'T; 'J_1['t];  x: 'A['t]; 'J_2['x;'t] >- 't = 't1 in 'T } -->
   [main] ('c : sequent ['ext] { 'H; t:'T; 'J_1['t];  x: 'A['t1]; 'J_2['x;'t] >- 'C['x;'t] }) -->
   sequent ['ext] { 'H; t:'T; 'J_1['t];  x: 'A['t]; 'J_2['x;'t] >- 'C['x;'t] } =
   'c

prim contextSubstPointwise 'H 'J_1 'J 't1  :
   [equality] sequent ['ext] { 'H; t:'T; 'J_1['t];  'J['t]; 'J_2['t] >- 't = 't1 in 'T } -->
   [main] ('c : sequent ['ext] { 'H; t:'T; 'J_1['t];  'J['t1]; 'J_2['t] >- 'C['t] }) -->
   sequent ['ext] { 'H; t:'T; 'J_1['t];  'J['t]; 'J_2['t] >- 'C['t] } =
   'c

doc <:doc< @docoff >>
