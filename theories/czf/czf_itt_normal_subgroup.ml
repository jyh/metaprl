include Czf_itt_group
include Czf_itt_subgroup
include Czf_itt_abel_group
include Czf_itt_coset

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

(*
 * A subgroup H of a group G is normal if its left and right cosets
 * coincide, that is, if gH = Ha for all g in G.
 *)
declare normal_subg{'s; 'g}

prim_rw unfold_normal_subg : normal_subg{'s; 'g} <-->
   (subgroup{'s; 'g} & (all a: set. (mem{'a; car{'g}} => equal{lcoset{'s; 'g; 'a}; rcoset{'s; 'g; 'a}})))

dform normal_subg_df : except_mode[src] :: normal_subg{'s; 'g} =
   `"normal_subgroup(" slot{'s} `"; " slot{'g} `")"

(*
 * There is a standared way to show that two sets are equal;
 * show that each is a subset of the other.
 *)
interactive equal_subset 'H :
   sequent [squash] { 'H >- isset{'x} } -->
   sequent [squash] { 'H >- isset{'y} } -->
   sequent ['ext] { 'H >- subset{'x; 'y} } -->
   sequent ['ext] { 'H >- subset{'y; 'x} } -->
   sequent ['ext] { 'H >- equal{'x; 'y} }

let equalSubsetT p =
   equal_subset (hyp_count_addr p) p

interactive normalSubg_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- "type"{normal_subg{'s; 'g}} }

interactive normalSubg_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} } -->
   sequent ['ext] { 'H; a: set; x: mem{'a; car{'g}} >- equal{lcoset{'s; 'g; 'a}; rcoset{'s; 'g; 'a}} } -->
   sequent ['ext] { 'H >- normal_subg{'s; 'g} }

(*interactive normalSubg_intro2 'H :
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} } -->
   sequent ['ext] { 'H; a: set; x: mem{'a; car{'g}} >- subset{lcoset{'s; 'g; 'a}; rcoset{'s; 'g; 'a}} } -->
   sequent ['ext] { 'H; b: set; x: mem{'b; car{'g}} >- subset{rcoset{'s; 'g; 'b}; lcoset{'s; 'g; 'b}} } -->
   sequent ['ext] { 'H >- normal_subg{'s; 'g} }
*)

(*
 * All subgroups of abelian groups are normal.
 *)
interactive abel_normalSubg 'H 'J 's :
   sequent [squash] { 'H; x: abel{'g}; 'J['x] >- 's IN label } -->
   sequent [squash] { 'H; x: abel{'g}; 'J['x] >- 'g IN label } -->
   sequent ['ext] { 'H; x: abel{'g}; 'J['x] >- subgroup{'s; 'g} } -->
   sequent ['ext] { 'H; x: abel{'g}; 'J['x]; y: normal_subg{'s; 'g} >- 'C['x] } -->
   sequent ['ext] { 'H; x: abel{'g}; 'J['x] >- 'C['x] }

let abelNormalSubgT t i p =
   let j, k = Sequent.hyp_indices p i in
      abel_normalSubg j k t p
