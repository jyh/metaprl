extends Itt_squash
extends Itt_ext_equal
extends Itt_struct2
extends Itt_subtype
extends Itt_pointwise

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
open Itt_pointwise

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(* This rule is valid both in pointwise and pairwise functionality, but the proof of this rule is
 * difirent for these functionalities
 *)
rule substUsingEpimorphism 'H 'J 'B bind{y. 'f['y]} bind{x. 'g['x]}  : (* g does not depend on J *)
   [wf] sequent [squash] { 'H; x: 'A; 'J['x]; y: 'B >- 'f['y] IN 'A } -->
   [wf] sequent [squash] { 'H; x: 'A; 'J['x] >-  'g['x] IN 'B } -->
   [equality] sequent [squash] { 'H; x: 'A; 'J['x] >- 'f['g['x]] ~ 'x } -->
   [main] sequent ['ext] { 'H; y: 'B; 'J['f['y]] >- 'C['f['y]] } -->
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'C['x] }

rule hypReplacementStrong 'H 'J 'B 'y :
   [assertion] sequent [squash] { 'H; x: 'A; 'J['x]; y: 'B >- 'y IN 'A } -->
   [assertion] sequent [squash] { 'H; x: 'A; 'J['x] >-  'x IN 'B } -->
   [main] sequent ['ext] { 'H; x: 'B; 'J['x] >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'C['x] }

rule hypReplacementExt 'H 'J 'B  :
   [equality] sequent [squash] { 'H; x: 'A; 'J['x] >- ext_equal{'A;'B} } -->
   [main]  sequent ['ext] { 'H; x: 'B; 'J['x] >- 'T['x] } -->
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'T['x] }

topval changeHypT : term -> int -> tactic

topval replaceHypT : term -> int -> tactic


