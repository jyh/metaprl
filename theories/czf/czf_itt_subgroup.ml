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

(* subgroup{'g; 's} is a type representing the subgroup
 * of the group represented by 'g, where 's is a label
 * representing the subgroup which itself is also a group.
 *)
declare subgroup{'g; 's}

prim_rw unfold_subgroup : subgroup{'g; 's} <-->
   (group{'g} & group{'s} & subset{car{'s}; car{'g}} & (all a: set. all b:set. (mem{'a; car{'s}} => mem{'b; car{'s}} => equal{op{'s; 'a; 'b}; op{'g; 'a; 'b}})))

dform subgroup_df : except_mode[src] :: subgroup{'g; 's} =
   `"subgroup(" slot{'g} `"; " slot{'s} `")"

(*
 * Axioms
 *)
interactive subgroup_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- group{'s} } -->
   sequent ['ext] { 'H >- "type"{subgroup{'g; 's}} }

interactive subgroup_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- group{'s} } -->
   sequent ['ext] { 'H >- subset{car{'s}; car{'g}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: mem{'a; car{'s}}; y: mem{'b; car{'s}} >- equal{op{'s; 'a; 'b}; op{'g; 'a; 'b}} } -->
   sequent ['ext] { 'H >- subgroup{'g; 's} }

interactive subgroup_equiv_elim {| elim [] |} 'H 'J 's :
   sequent [squash] { 'H; x: equiv{car{'g}; 'R}; 'J['x] >- 'g IN label } -->
   sequent [squash] { 'H; x: equiv{car{'g}; 'R}; 'J['x] >- 's IN label } -->
   sequent [squash] { 'H; x: equiv{car{'g}; 'R}; 'J['x] >- isset{'R} } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R}; 'J['x] >- subgroup{'g; 's} } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R}; 'J['x]; y: equiv{car{'s}; 'R} >- 'C['x] } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R}; 'J['x] >- 'C['x] }

interactive subgroup_id {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent ['ext] { 'H >- subgroup{'g; 's} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; id{'s}; id{'g}} }

interactive subgroup_inv {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'s}} } -->
   sequent ['ext] { 'H >- subgroup{'g; 's} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; inv{'s; 'a}; inv{'g; 'a}} }

(* Properties *)
(* The intersections of subgroups H1 and H2 of a group G is again a subgroup of G. *)
interactive subgroup_isect 'H 'h1 'h2 :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 'h1 IN label } -->
   sequent [squash] { 'H >- 'h2 IN label } -->
   sequent [squash] { 'H >- 'h IN label } -->
   sequent ['ext] { 'H >- group{'h} } -->
   sequent ['ext] { 'H >- subgroup{'g; 'h1} } -->
   sequent ['ext] { 'H >- subgroup{'g; 'h2} } -->
   sequent ['ext] { 'H >- equal{car{'h}; ."isect"{car{'h1}; car{'h2}}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: mem{'a; car{'h}}; x: mem{'b; car{'h}} >- equal{op{'h; 'a; 'b}; op{'g; 'a; 'b}} } -->
   sequent ['ext] { 'H >- subgroup{'g; 'h} }

let subgroupIsectT t1 t2 p =
   subgroup_isect (hyp_count_addr p) t1 t2 p
