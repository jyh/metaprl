include Czf_itt_equiv
include Czf_itt_eq
include Czf_itt_group
include Czf_itt_subset
include Czf_itt_isect

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Sequent
open Tactic_type.Tacticals
open Var
open Mptop

open Base_dtactic
open Base_auto_tactic

(* subgroup{'s; 'g} is a type representing the subgroup
 * of the group represented by 'g, where 's is a label
 * representing the subgroup which itself is also a group.
 *)
declare subgroup{'s; 'g}

prim_rw unfold_subgroup : subgroup{'s; 'g} <-->
   (group{'s} & group{'g} & subset{car{'s}; car{'g}} & (all a: set. all b: set. (mem{'a; car{'s}} => mem{'b; car{'s}} => equal{op{'s; 'a; 'b}; op{'g; 'a; 'b}})) & (all a: set. all b: set. (equiv{car{'s}; eqG{'s}; 'a; 'b} => equiv{car{'g}; eqG{'g}; 'a; 'b})))

dform subgroup_df : except_mode[src] :: subgroup{'s; 'g} =
   `"subgroup(" slot{'s} `"; " slot{'g} `")"

(*
 * Axioms
 *)
interactive subgroup_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- "type"{subgroup{'s; 'g}} }

interactive subgroup_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'s} } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- subset{car{'s}; car{'g}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: mem{'a; car{'s}}; y: mem{'b; car{'s}} >- equal{op{'s; 'a; 'b}; op{'g; 'a; 'b}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: equiv{car{'s}; eqG{'s}; 'a; 'b} >- equiv{car{'g}; eqG{'g}; 'a; 'b} } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} }

interactive subgroup_equiv {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} } -->
   sequent ['ext] { 'H >- equiv{car{'s}; eqG{'g}} }

interactive subgroup_id {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; eqG{'g}; id{'s}; id{'g}} }

interactive subgroup_inv {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'s}} } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; eqG{'g}; inv{'s; 'a}; inv{'g; 'a}} }

(* Properties *)
(* The intersections of subgroups H1 and H2 of a group G is again a subgroup of G. *)
interactive subgroup_isect 'H 'h1 'h2 :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 'h1 IN label } -->
   sequent [squash] { 'H >- 'h2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent ['ext] { 'H >- group{'h} } -->
   sequent ['ext] { 'H >- subgroup{'h1; 'g} } -->
   sequent ['ext] { 'H >- subgroup{'h2; 'g} } -->
   sequent ['ext] { 'H >- equal{car{'h}; ."isect"{car{'h1}; car{'h2}}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: mem{'a; car{'h}}; x: mem{'b; car{'h}} >- equal{op{'h; 'a; 'b}; op{'h1; 'a; 'b}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: equiv{car{'h}; eqG{'h}; 'a; 'b} >- equiv{car{'h1}; eqG{'h1}; 'a; 'b} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g} }

let subgroupIsectT t1 t2 p =
   subgroup_isect (hyp_count_addr p) t1 t2 p
