include Czf_itt_sep

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

(* The inverse image of t in s: { x in s | a(x) in t } *)
declare inv_image{'s; x. 'a['x]; 't}

prim_rw unfold_inv_image: inv_image{'s; x. 'a['x]; 't} <-->
   sep{'s; x. mem{'a['x]; 't}}

let fold_inv_image = makeFoldC << inv_image{'s; x. 'a['x]; 't} >> unfold_inv_image

dform inv_image_df : parens :: except_mode[src] :: inv_image{'s; x. 'a; 't} =
   pushm[0] `"{" slot{'x} " " Nuprl_font!member `"s " slot{'s} mid slot{'a} " " Nuprl_font!member `"s " slot{'t} `"}" popm

interactive inv_image_isset {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'t} } -->
   sequent ['ext] { 'H >- fun_set{z. 'a['z]} } -->
   sequent ['ext] { 'H >- isset{inv_image{'s; x. 'a['x]; 't}} }

interactive inv_image_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'y} } -->
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'t} } -->
   sequent ['ext] { 'H >- fun_set{x. 'a['x]} } -->
   sequent ['ext] { 'H >- mem{'y; 's} } -->
   sequent ['ext] { 'H >- mem{'a['y]; 't} } -->
   sequent ['ext] { 'H >- mem{'y; inv_image{'s; x. 'a['x]; 't}} }

interactive inv_image_elim {| elim [] |} 'H 'J :
   sequent [squash] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x] >- isset{'y} } -->
   sequent [squash] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x] >- isset{'t} } -->
   sequent ['ext] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x] >- fun_set{x. 'a['x]} } -->
   sequent ['ext] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x]; v: mem{'y; 's}; w: mem{'a['y]; 't} >- 'C['x] } -->
   sequent ['ext] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x] >- 'C['x] }
