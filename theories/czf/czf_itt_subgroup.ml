include Czf_itt_group
include Czf_itt_subset
include Czf_itt_isect

open Refiner.Refiner
open Var

open Base_dtactic
open Base_auto_tactic

declare subgroup

dform subgroup_df : except_mode[src] :: subgroup =
   `"subG"

(* axioms *)
interactive subgroup_wf1 {| intro[] |} 'H :
   sequent ['ext] { 'H >- isset{subgroup} }

interactive subgroup_wf2 {| intro[] |} 'H :
   sequent ['ext] { 'H >- subset{subgroup; car} }

interactive subgroup_op_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'s1; subgroup} } -->
   sequent ['ext] { 'H >- mem{'s2; subgroup} } -->
   sequent ['ext] { 'H >- mem{op{'s1; 's2}; subgroup} }

interactive subgroup_id_wf {| intro[] |} 'H :
   sequent ['ext] { 'H >- mem{id; subgroup} }

interactive subgroup_inv_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- mem{'s; subgroup} } -->
   sequent ['ext] { 'H >- mem{inv{'s}; subgroup} }

(* Properties *)
(* The intersections of subgroups H1 and H2 of a group G is again a subgroup of G. *)
interactive subgroup_isect_wf1 {| intro[] |} 'H :
   sequent ['ext] { 'H >- isset{'subg1} } -->
   sequent ['ext] { 'H >- isset{'subg2} } -->
   sequent ['ext] { 'H >- isset{."isect"{'subg1; 'subg2}} }

interactive subgroup_isect_wf2 {| intro[] |} 'H :
   sequent ['ext] { 'H >- isset{'subg1} } -->
   sequent ['ext] { 'H >- isset{'subg2} } -->
   sequent ['ext] { 'H >- subset{'subg1; car} } -->
   sequent ['ext] { 'H >- subset{'subg2; car} } -->
   sequent ['ext] { 'H >- subset{."isect"{'subg1; 'subg2}; car} }

interactive subgroup_op_wf1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'subg1} } -->
   sequent [squash] { 'H >- isset{'subg2} } -->
   sequent ['ext] { 'H >- subset{'subg1; car} } -->
   sequent ['ext] { 'H >- subset{'subg2; car} } -->
   sequent ['ext] { 'H; s1: set; t1: set; x1: mem{'s1; 'subg1}; y1: mem{'t1; 'subg1} >- mem{op{'s1; 't1}; 'subg1} } -->
   sequent ['ext] { 'H; s2: set; t2: set; x2: mem{'s2; 'subg2}; y2: mem{'t2; 'subg2} >- mem{op{'s2; 't2}; 'subg2} } -->
   sequent ['ext] { 'H; s: set; t: set; x: mem{'s; ."isect"{'subg1; 'subg2}}; y: mem{'t; ."isect"{'subg1; 'subg2}} >- mem{op{'s; 't}; ."isect"{'subg1; 'subg2}} }

interactive subgroup_id_wf1 {| intro[] |} 'H :
   sequent ['ext] { 'H >- isset{'subg1} } -->
   sequent ['ext] { 'H >- isset{'subg2} } -->
   sequent ['ext] { 'H >- subset{'subg1; car} } -->
   sequent ['ext] { 'H >- subset{'subg2; car} } -->
   sequent ['ext] { 'H >- mem{id; 'subg1} } -->
   sequent ['ext] { 'H >- mem{id; 'subg2} } -->
   sequent ['ext] { 'H >- mem{id; ."isect"{'subg1; 'subg2}} }

interactive subgroup_inv_wf1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'subg1} } -->
   sequent [squash] { 'H >- isset{'subg2} } -->
   sequent ['ext] { 'H >- subset{'subg1; car} } -->
   sequent ['ext] { 'H >- subset{'subg2; car} } -->
   sequent ['ext] { 'H; s: set; x: mem{'s; 'subg1} >- mem{inv{'s}; 'subg1} } -->
   sequent ['ext] { 'H; s: set; x: mem{'s; 'subg2} >- mem{inv{'s}; 'subg2} } -->
   sequent ['ext] { 'H; s: set; x: mem{'s; ."isect"{'subg1; 'subg2}} >- mem{inv{'s}; ."isect"{'subg1; 'subg2}} }
