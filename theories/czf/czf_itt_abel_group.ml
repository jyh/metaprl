include Czf_itt_group

open Refiner.Refiner
open Simple_print
open Var

open Base_dtactic
open Base_auto_tactic

(* axioms *)
interactive op_commut {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'s1; car} } -->
   sequent ['ext] { 'H >- mem{'s2; car} } -->
   sequent ['ext] { 'H >- equal{op{'s1; 's2}; op{'s2; 's1}} }
