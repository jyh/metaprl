include Itt_squash
include Itt_ext_equal
include Itt_struct2
include Itt_subtype
include Itt_pointwise

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
open Itt_struct
open Itt_pointwise

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_struct%t"

(* debug_string DebugLoad "Loading itt_struct..." *)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(* This rule is valid both in pointwise and pairwise functionality, but the proof of this rule is
 * difirent for these functionalities
 *)


interactive substUsingEpimorphism 'H 'J 'B bind{y. 'f['y]} bind{x. 'g['x]}  : (* g does not depend on J *)
   [wf] sequent [squash] { 'H; x: 'A; 'J['x]; y: 'B >- 'f['y] IN 'A } -->
   [wf] sequent [squash] { 'H; x: 'A; 'J['x] >-  'g['x] IN 'B } -->
   [equality] sequent [squash] { 'H; x: 'A; 'J['x] >- 'f['g['x]] ~ 'x } -->
   [main] sequent ['ext] { 'H; y: 'B; 'J['f['y]] >- 'C['f['y]] } -->
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'C['x] }

interactive hypReplacementStrong 'H 'J 'B 'y:
   [assertion] sequent [squash] { 'H; x: 'A; 'J['x]; y: 'B >- 'y IN 'A } -->
   [assertion] sequent [squash] { 'H; x: 'A; 'J['x] >-  'x IN 'B } -->
   [main] sequent ['ext] { 'H; x: 'B; 'J['x] >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'C['x] }

interactive hypReplacementExt 'H 'J 'B  :
   [equality] sequent [squash] { 'H; x: 'A; 'J['x] >- ext_equal{'A;'B} } -->
   [main]  sequent ['ext] { 'H; x: 'B; 'J['x] >- 'T['x] } -->
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'T['x] }

let changeHypT t i p =
   let y = maybe_new_vars1 p "y" in
   let j, k = Sequent.hyp_indices p i in
      hypReplacementStrong j k t y p

let replaceHypT t i p =
   let j, k = Sequent.hyp_indices p i in
   try
      let univ = get_univ_arg p in
        hypReplacement j k t univ p
   with RefineError _ ->
        hypReplacementExt j k t p

