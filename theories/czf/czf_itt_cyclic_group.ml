include Czf_itt_equiv
include Czf_itt_group
include Czf_itt_cyclic_subgroup
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
open Simple_print

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

declare cycgroup{'g; 'a}

prim_rw unfold_cycgroup : cycgroup{'g; 'a} <-->
   (group{'g} & mem{'a; car{'g}} & equal{car{'g}; collect{int; x. power{'g; 'a; 'x}}})

let fold_cycgroup = makeFoldC << cycgroup{'g; 'a} >> unfold_cycgroup

dform cyclic_group_df : except_mode[src] :: cycgroup{'g; 'a} =
   `"cyclic_group(" slot{'g} `"; " slot{'a} `")"

interactive cycgroup_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- "type"{cycgroup{'g; 'a}} }

interactive cycgroup_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- equal{car{'g}; collect{int; x. power{'g; 'a; 'x}}} } -->
   sequent ['ext] { 'H >- cycgroup{'g; 'a} }

(* Every cyclic group is abelian *)
interactive cycgroup_abel 'H 'a :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- cycgroup{'g; 'a} } -->
   sequent ['ext] { 'H >- abel{'g} }

let cycgroupAbelT t p =
   cycgroup_abel (hyp_count_addr p) t p
