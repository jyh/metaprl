include Czf_itt_group
include Czf_itt_subset

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
