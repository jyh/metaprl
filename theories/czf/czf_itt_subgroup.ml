include Czf_itt_group
include Czf_itt_subset
include Czf_itt_isect

open Refiner.Refiner
open Var

open Base_dtactic
open Base_auto_tactic

(* subgroup{'g; 's} is a label representing the subgroup
 * of the group represented by 'g, with 's representing
 * the specific subgroup.
 *)
declare subgroup{'g; 's}

dform subgroup_df : except_mode[src] :: subgroup{'g; 's} =
   `"subgroup(" slot{'g} `"; " slot{'s} `")"

(* Axioms *)
interactive subgroup_wf1 {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent ['ext] { 'H >- subgroup{'g; 's} IN label }

interactive subgroup_wf2 {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- group{subgroup{'g; 's}} }

interactive subgroup_car_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- subset{car{subgroup{'g; 's}}; car{'g}} }

interactive subgroup_op_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'s1; car{subgroup{'g; 's}}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{subgroup{'g; 's}}} } -->
   sequent ['ext] { 'H >- mem{op{'g; 's1; 's2}; car{subgroup{'g; 's}}} }

interactive subgroup_id_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{id{'g}; car{subgroup{'g; 's}}} }

interactive subgroup_inv_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{subgroup{'g; 's}}} } -->
   sequent ['ext] { 'H >- mem{inv{'g; 'a}; car{subgroup{'g; 's}}} }

(* Properties *)
(* The intersections of subgroups H1 and H2 of a group G is again a subgroup of G. *)
interactive subgroup_isect_subset {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's1 IN label } -->
   sequent [squash] { 'H >- 's2 IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- subset{."isect"{car{subgroup{'g; 's1}}; car{subgroup{'g; 's2}}}; car{'g}} }

interactive subgroup_isect_op {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's1 IN label } -->
   sequent [squash] { 'H >- 's2 IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent ['ext] { 'H >- mem{'a; ."isect"{car{subgroup{'g; 's1}}; car{subgroup{'g; 's2}}}} } -->
   sequent ['ext] { 'H >- mem{'b; ."isect"{car{subgroup{'g; 's1}}; car{subgroup{'g; 's2}}}} } -->
   sequent ['ext] { 'H >- mem{op{'g; 'a; 'b}; ."isect"{car{subgroup{'g; 's1}}; car{subgroup{'g; 's2}}}} }

interactive subgroup_isect_id {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's1 IN label } -->
   sequent [squash] { 'H >- 's2 IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{id{'g}; ."isect"{car{subgroup{'g; 's1}}; car{subgroup{'g; 's2}}}} }

interactive subgroup_isect_inv {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's1 IN label } -->
   sequent [squash] { 'H >- 's2 IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; ."isect"{car{subgroup{'g; 's1}}; car{subgroup{'g; 's2}}}} } -->
   sequent ['ext] { 'H >- mem{inv{'g; 'a}; ."isect"{car{subgroup{'g; 's1}}; car{subgroup{'g; 's2}}}} }
