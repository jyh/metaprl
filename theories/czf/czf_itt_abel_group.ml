include Czf_itt_group

open Refiner.Refiner
open Simple_print
open Var

open Base_dtactic
open Base_auto_tactic

declare abel{'g}

dform abel_df : except_mode[src] :: abel{'g} =
   `"abel(" slot{'g} `")"

(* axioms *)
interactive abel_wf {| intro[] |} 'H 's1 's2:
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- equal{op{'g; 's1; 's2}; op{'g; 's2; 's1}} } -->
   sequent ['ext] { 'H >- abel{'g} }
