include Czf_itt_dall
include Czf_itt_dexists

open Printf
open Mp_debug
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

declare set_bvd{'s; x. 'a['x]}            (* { a(x) | x in s } *)
declare setbvd_prop{'s; x. 'p['x]}        (* { x in s | p(x) } *)

prim_rw unfold_set_bvd: set_bvd{'s; x. 'a['x]} <-->
   set_ind{'s; t, f, g. collect{'t; y. 'a['f 'y]}}

interactive_rw reduce_set_bvd : set_bvd{collect{'T; x. 'f['x]}; x. 'a['x]} <-->
   collect{'T; y. 'a['f['y]]}

let resource reduce += << set_bvd{collect{'T; x. 'f['x]}; x. 'a['x]} >>, reduce_set_bvd

dform set_bvd_df : parens :: except_mode[src] :: set_bvd{'s; x. 'a} =
   pushm[0] `"{" slot{'a} `" | " slot{'x} " " Nuprl_font!member `"s " slot{'s} `"}" popm

dform setbvd_prop_df : parens :: except_mode[src] :: setbvd_prop{'s; x. 'p} =
   pushm[0] `"{" slot{'x} " " Nuprl_font!member `"s " slot{'s} `" | " slot{'p} `"}" popm

(*
 * Propertiess for set builder.
 *)
interactive set_bvd_isset {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; x: set >- isset{'a['x]} } -->
   sequent ['ext] { 'H >- isset{set_bvd{'s; x. 'a['x]}} }

interactive set_bvd_member_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'y} } -->
   sequent [squash] { 'H; x: set >- isset{'a['x]} } -->
   sequent ['ext] { 'H >- fun_set{x. 'a['x]} } -->
   sequent ['ext] { 'H >- dexists{'s; z. eq{'y; 'a['z]}} } -->
   sequent ['ext] { 'H >- mem{'y; set_bvd{'s; x. 'a['x]}} }

interactive set_bvd_member_elim {| elim [] |} 'H 'J :
   sequent [squash] { 'H; x: mem{'y; set_bvd{'s; x. 'a['x]}}; 'J['x] >- isset{'y} } -->
   sequent [squash] { 'H; x: mem{'y; set_bvd{'s; x. 'a['x]}}; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: mem{'y; set_bvd{'s; x. 'a['x]}}; 'J['x]; z: set >- isset{'a['z]} } -->
   sequent ['ext] { 'H; x: mem{'y; set_bvd{'s; x. 'a['x]}}; 'J['x] >- fun_set{x. 'a['x]} } -->
   sequent ['ext] { 'H; x: mem{'y; set_bvd{'s; x. 'a['x]}}; 'J['x]; z: set; u: mem{'z; 's}; v: eq{'y; 'a['z]} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; set_bvd{'s; x. 'a['x]}}; 'J['x] >- 'T['x] }

interactive set_bvd_fun {| intro [] |} 'H :
   sequent ['ext] { 'H >- fun_set{z. 'A['z]} } -->
   sequent ['ext] { 'H; z: set >- fun_set{x. 'B['z; 'x]} } -->
   sequent ['ext] { 'H; z: set >- fun_set{x. 'B['x; 'z]} } -->
   ["wf"] sequent [squash] { 'H; z: set; x: set >- isset{'B['z; 'x]} } -->
   sequent ['ext] { 'H >- fun_set{z. set_bvd{'A['z]; y. 'B['z; 'y]}} }

(*
 * Axioms for setbvd_prop.
 *)
interactive setbvd_prop_isset {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; x: set >- "type"{'p['x]} } -->
   sequent ['ext] { 'H >- isset{setbvd_prop{'s; x. 'p['x]}} }

interactive setbvd_prop_member_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'y} } -->
   sequent [squash] { 'H; z: set >- "type"{'p['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'p['z]} } -->
   sequent ['ext] { 'H >- mem{'y; 's} } -->
   sequent ['ext] { 'H >- 'p['y] } -->
   sequent ['ext] { 'H >- mem{'y; setbvd_prop{'s; x. 'p['x]}} }

interactive setbvd_prop_member_elim {| elim [] |} 'H 'J :
   sequent [squash] { 'H; u: mem{'y; setbvd_prop{'s; x. 'p['x]}}; 'J['u] >- isset{'s} } -->
   sequent [squash] { 'H; u: mem{'y; setbvd_prop{'s; x. 'p['x]}}; 'J['u] >- isset{'y} } -->
   sequent [squash] { 'H; u: mem{'y; setbvd_prop{'s; x. 'p['x]}}; 'J['u]; z: set >- "type"{'p['z]} } -->
   sequent ['ext] { 'H; u: mem{'y; setbvd_prop{'s; x. 'p['x]}}; 'J['u] >- fun_prop{z. 'p['z]} } -->
   sequent ['ext] { 'H; u: mem{'y; setbvd_prop{'s; x. 'p['x]}}; 'J['u]; v: mem{'y; 's}; w: 'p['y] >- 'C['u] } -->
   sequent ['ext] { 'H; u: mem{'y; setbvd_prop{'s; x. 'p['x]}}; 'J['u] >- 'C['u] }
