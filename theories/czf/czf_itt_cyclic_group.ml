include Czf_itt_group
include Czf_itt_cyclic_subgroup
include Czf_itt_subgroup
include Czf_itt_subset
include Itt_logic

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

declare cyclic{'g; 'a}

prim_rw unfold_cyclic : cyclic{'g; 'a} <-->
   cyclic_subgroup{'g; 'a}

let fold_cyclic = makeFoldC << cyclic{'g; 'a} >> unfold_cyclic

dform cyclic_group_df : except_mode[src] :: cyclic{'g; 'a} =
   `"<" slot{'a} `">" subc

(* axioms *)
interactive cyclic_group_def {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- equal{cyclic{'g; 'a}; car{'g}} }

(* basic properties of cyclic groups *)
interactive cyclic_group_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >-  isset{cyclic{'g; 'a}} }

interactive cyclic_group_op_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'s1; cyclic{'g; 'a}} } -->
   sequent ['ext] { 'H >- mem{'s2; cyclic{'g; 'a}} } -->
   sequent ['ext] { 'H >- mem{op{'g; 's1; 's2}; cyclic{'g; 'a}} }

interactive cyclic_group_id_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- mem{id{'g}; cyclic{'g; 'a}} }

interactive cyclic_group_inv_wf1 {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- mem{'s; cyclic{'g; 'a}} } -->
   sequent ['ext] { 'H >- mem{inv{'g; 's}; cyclic{'g; 'a}} }

(* Every cyclic group is abelian *)
interactive cyclic_group_abel {| intro[] |} 'H 'a :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'s1; cyclic{'g; 'a}} } -->
   sequent ['ext] { 'H >- mem{'s2; cyclic{'g; 'a}} } -->
   sequent ['ext] { 'H >- equal{op{'g; 's1; 's2}; op{'g; 's2; 's1}} }
