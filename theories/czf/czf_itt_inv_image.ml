include Czf_itt_set
include Czf_itt_member

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

declare inv_image{'s; x. 'a['x]; 't}  (* { x in s | a(x) in t } *)

dform inv_image_df : parens :: except_mode[src] :: inv_image{'s; x. 'a; 't} =
   pushm[0] `"{" slot{'x} Nuprl_font!member `"s " slot{'s} `"| " slot{'a} " " Nuprl_font!member `"s " slot{'t} `"}" popm

(*
 * Axioms for inverse image.
 *)
interactive inv_image_isset {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'t} } -->
   sequent [squash] { 'H; x: set >- isset{'a['x]} } -->
   sequent ['ext] { 'H >- isset{inv_image{'s; x. 'a['x]; 't}} }

interactive inv_image_member_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'y} } -->
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'t} } -->
   sequent [squash] { 'H; x: set >- isset{'a['x]} } -->
   sequent ['ext] { 'H >- fun_set{x. 'a['x]} } -->
   sequent ['ext] { 'H >- mem{'y; 's} } -->
   sequent ['ext] { 'H >- mem{'a['y]; 't} } -->
   sequent ['ext] { 'H >- mem{'y; inv_image{'s; x. 'a['x]; 't}} }

interactive inv_image_member_elim {| elim [] |} 'H 'J :
   sequent [squash] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x] >- isset{'y} } -->
   sequent [squash] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x] >- isset{'t} } -->
   sequent ['ext] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x]; z: set >- isset{'a['z]} } -->
   sequent ['ext] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x] >- fun_set{x. 'a['x]} } -->
   sequent ['ext] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x] >- mem{'y; 's} } -->
   sequent ['ext] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x]; w: mem{'a['y]; 't} >- 'C['x] } -->
   sequent ['ext] { 'H; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; 'J['x] >- 'C['x] }
