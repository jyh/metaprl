include Czf_itt_group
include Czf_itt_equiv
include Czf_itt_hom

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
open Simple_print

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

declare iso{'g1; 'g2; x. 'f['x]}

dform iso_df : parens :: except_mode[src] :: iso{'g1; 'g2; x. 'f} =
   `"iso(" slot{'g1} `"; " slot{'g2} `"; " slot{'f} `")"

(*
 * An isomorphism f: G1 -> G2 is a homomorphism that is
 * one-to-one and onto G2. That is, an isomorphism
 * f: G1 -> G2 is a homomorphism where f is a bijection.
 *)
prim_rw unfold_iso : iso{'g1; 'g2; x. 'f['x]} <-->
   (hom{'g1; 'g2; x. 'f['x]} & (all c: set. all d: set. (mem{'c; car{'g1}} => mem{'d; car{'g1}} => equiv{car{'g2}; eqG{'g2}; 'f['c]; 'f['d]} => equiv{car{'g1}; eqG{'g1}; 'c; 'd})) & (all e: set. (mem{'e; car{'g2}} => (exst p: set. (mem{'p; car{'g1}} & equiv{car{'g2}; eqG{'g2}; 'e; 'f['p]})))))

interactive iso_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H; x: set >- isset{'f['x]} } -->
   sequent ['ext] { 'H >- "type"{iso{'g1; 'g2; x. 'f['x]}} }

(*interactive iso_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H; x: set >- isset{'f['x]} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; x. 'f['x]} } -->
   sequent ['ext] { 'H; a: set; b: set; u: mem{'a; car{'g1}}; v: mem{'b; car{'g1}}; u: equiv{car{'g2}; eqG{'g2}; 'f['a]; 'f['b]} >- equiv{car{'g1}; eqG{'g1}; 'a; 'b} } -->
   sequent ['ext] { 'H; c: set; w: mem{'c; car{'g2}} >- (exst d: set. (mem{'d; car{'g1}} => equiv{car{'g2}; eqG{'g2}; 'c; 'f['d]})) } -->
   sequent ['ext] { 'H >- iso{'g1; 'g2; x. 'f['x]} }
*)

interactive iso_fun {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent ['ext] { 'H; z: set; x1: set; y1: mem{'x1; car{'g1}} >- mem{'f['z; 'x1]; car{'g2}} } -->
   sequent ['ext] { 'H; z: set >- fun_set{x. 'f['x; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. iso{'g1; 'g2; y. 'f['z; 'y]}} }

interactive iso_equiv_fun {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent [squash] { 'H; z: set; x: set >- isset{'f['z; 'x]} } -->
   sequent ['ext] { 'H; z1: set; x1: set; y1: mem{'x1; car{'g1}} >- mem{'f['z1; 'x1]; car{'g2}} } -->
   sequent ['ext] { 'H; z3: set; c: set; d: set; x3: mem{'c; car{'g1}}; y3: mem{'d; car{'g1}}; v: equiv{car{'g1}; eqG{'g1}; 'c; 'd} >- equiv{car{'g2}; eqG{'g2}; 'f['c; 'z3]; 'f['d; 'z3]} } -->
   sequent ['ext] { 'H >- equiv_fun_prop{car{'g1}; eqG{'g1}; z. iso{'g1; 'g2; y. 'f['z; 'y]}} }
