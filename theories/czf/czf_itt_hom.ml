include Czf_itt_set
include Czf_itt_group
include Czf_itt_equiv
include Czf_itt_abel_group

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

declare hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]}

dform hom_df : parens :: except_mode[src] :: hom{'g1; 'g2; 'r1; 'r2; x. 'f} =
   `"hom(" slot{'g1} `"; " slot{'g2} `"; " slot{'r1} `"; " slot{'r2} `"; " slot{'f} `")"

(*
 * g1 and g2 are groups; r1 and r2 are equivalence
 * relations on g1 and g2; f is a map of g1 into g2;
 * and for all a, b in g1, f(a * b) = f(a) * f(b).
 *)
prim_rw unfold_hom : hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]} <-->
   (group{'g1} & group{'g2} & isset{'r1} & isset{'r2} & equiv{car{'g1}; 'r1} & equiv{car{'g2}; 'r2} & fun_set{x. 'f['x]} & "dall"{car{'g1}; a. mem{'f['a]; car{'g2}}} & (all a: set. all b: set. (mem{'a; car{'g1}} => mem{'b; car{'g1}} => equiv{car{'g2}; 'r2; 'f[op{'g1; 'a; 'b}]; op{'g2; 'f['a]; 'f['b]}})))

interactive hom_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent [squash] { 'H >- isset{'r1} } -->
   sequent [squash] { 'H >- isset{'r2} } -->
   sequent [squash] { 'H; x: set >- isset{'f['x]} } -->
   sequent ['ext] { 'H >- "type"{hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]}} }

interactive hom_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f['z]} } -->
   sequent ['ext] { 'H; x: set; y: mem{'x; car{'g1}} >- mem{'f['x]; car{'g2}} } -->
   sequent [squash] { 'H >- isset{'r1} } -->
   sequent [squash] { 'H >- isset{'r2} } -->
   sequent ['ext] { 'H >- equiv{car{'g1}; 'r1} } -->
   sequent ['ext] { 'H >- equiv{car{'g2}; 'r2} } -->
   sequent ['ext] { 'H; a: set; b: set; x: mem{'a; car{'g1}}; y: mem{'b; car{'g1}} >- equiv{car{'g2}; 'r2; 'f[op{'g1; 'a; 'b}]; op{'g2; 'f['a]; 'f['b]}} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]} }

interactive hom_fun {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent ['ext] { 'H >- fun_set{z. 'r2['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'r1['z]} } -->
   sequent ['ext] { 'H; z: set >- fun_set{x. 'f['z; 'x]} } -->
   sequent ['ext] { 'H; z: set >- fun_set{x. 'f['x; 'z]} } -->
   sequent [squash] { 'H; z: set; x: set >- isset{'f['z; 'x]} } -->
   sequent ['ext] { 'H; z: set; x: set; y: mem{'x; car{'g1}} >- mem{'f['z; 'x]; car{'g2}} } -->
   sequent ['ext] { 'H >- fun_prop{z. hom{'g1; 'g2; 'r1['z]; 'r2['z]; y. 'f['z; 'y]}} }

(*
 * Trivial homomorphism
 * For any groups G and G', there is always at least one homomorphism
 * f: G - >G' defined by 'f('a) = e' for all a in G, where e' is the
 * identity in G'. This is called the trivial homomorphism.
 *)
interactive trivial_hom 'H :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent ['ext] { 'H >- group{'g1} } -->
   sequent ['ext] { 'H >- group{'g2} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f['z]} } -->
   sequent [squash] { 'H >- isset{'r1} } -->
   sequent [squash] { 'H >- isset{'r2} } -->
   sequent ['ext] { 'H >- equiv{car{'g1}; 'r1} } -->
   sequent ['ext] { 'H >- equiv{car{'g2}; 'r2} } -->
   sequent ['ext] { 'H; x: set; y: mem{'x; car{'g1}} >- equiv{car{'g2}; 'r2; 'f['x]; id{'g2}} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]} }

(*
 * Let f: G -> G' be a group homomorphism of G ONTO G'. If G is abelian,
 * then G' must be abelian.
 *)
interactive hom_abel 'H hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]} :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- isset{'r1} } -->
   sequent [squash] { 'H >- isset{'r2} } -->
   sequent ['ext] { 'H; x: set; y: mem{'x; car{'g2}} >- "dexists"{car{'g1}; z. equiv{car{'g2}; 'r2; 'x; 'f['z]}} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- abel{'g1; 'r1} } -->
   sequent ['ext] { 'H >- abel{'g2; 'r2} }

(*
 * properties
 *)
(*
 * Let f: G -> G' be a group homomorphism of G ONTO G'.
 * If e is the identity in G, then f(e) is the identity e' in G'.
 *)
interactive hom_id 'H hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]} :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- isset{'r1} } -->
   sequent [squash] { 'H >- isset{'r2} } -->
   sequent ['ext] { 'H >- hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]} } -->
   sequent ['ext] { 'H >- equiv{car{'g2}; 'r2; 'f[id{'g1}]; id{'g2}} }

(*
 * Let f: G -> G' be a group homomorphism of G ONTO G'.
 * For any a in G, f(inv(a)) = inv(f(a)).
 *)
interactive hom_inv 'H 'a hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]} :
   sequent [squash] { 'H >- 'g1 IN label } -->
   sequent [squash] { 'H >- 'g2 IN label } -->
   sequent [squash] { 'H >- isset{'r1} } -->
   sequent [squash] { 'H >- isset{'r2} } -->
(*   sequent [squash] { 'H; x: set >- isset{'f['x]} } -->*)
   sequent ['ext] { 'H >- hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g1}} } -->
   sequent ['ext] { 'H >- equiv{car{'g2}; 'r2; 'f[inv{'g1; 'a}]; inv{'g2; 'f['a]}} }
