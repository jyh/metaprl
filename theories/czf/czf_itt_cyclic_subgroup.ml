include Czf_itt_group
include Czf_itt_subgroup
include Czf_itt_subset
include Itt_int_base

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
open Printf
open Mp_debug

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

declare elem_in_G
declare power{'z; 'n}
declare cyclic_subgroup{elem_in_G}

prim_rw unfold_power : power{'z; 'n} <-->
   ind{'n; i, j. op{inv{'z}; power{'z; ('n +@ 1)}}; id; k, l. op{'z; power{'z; ('n -@ 1)}}}

prim_rw unfold_cyclic_subgroup : cyclic_subgroup{elem_in_G} <-->
   collect{int; x. power{elem_in_G; 'x}}

let fold_power = makeFoldC << power{'z; 'n} >> unfold_power
let fold_cyclic_subgroup = makeFoldC << cyclic_subgroup{elem_in_G} >> unfold_cyclic_subgroup

prec prec_power

dform elem_in_G_df : except_mode[src] :: elem_in_G =
   `"gen"

dform power_df : parens :: "prec"[prec_power] :: except_mode[src] :: power{'z; 'n} =
   slot["le"]{'z} `"^" slot{'n}

dform cyclic_subgroup_df : except_mode[src] :: cyclic_subgroup{elem_in_G} =
   `"<gen>"

(* axioms *)
interactive elem_in_G_wf1 {| intro [] |} 'H :
   sequent ['ext] { 'H >- isset{elem_in_G} }

interactive elem_in_G_wf2 {| intro [] |} 'H :
   sequent ['ext] { 'H >- mem{elem_in_G; car} }

(* power is a set *)
interactive power_wf1 {| intro [] |} 'H :
   sequent ['ext] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{'z} } -->
   sequent ['ext] { 'H >- mem{'z; car} } -->
   sequent ['ext] { 'H >- isset{power{'z; 'n}} }

(* the power of an element in G is also in G *)
interactive power_wf2 {| intro [] |} 'H :
   sequent ['ext] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{'z} } -->
   sequent ['ext] { 'H >- mem{'z; car} } -->
   sequent ['ext] { 'H >- mem{power{'z; 'n}; car} }

(* power{elem_in_G; 'n} is in G *)
interactive power_elem_in_G_wf1 {| intro [] |} 'H :
   sequent ['ext] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- mem{power{elem_in_G; 'n}; car} }

(* power property 1 *)
interactive power_property1 {| intro [] |} 'H :
   sequent ['ext] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car} } -->
   sequent ['ext] { 'H >- equal{op{power{'x; ('n +@ 1)}; inv{'x}}; power{'x; 'n}} }

(* power property 2 *)
interactive power_property2 {| intro [] |} 'H :
   sequent ['ext] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car} } -->
   sequent ['ext] { 'H >- equal{op{power{'x; 'n}; 'x}; power{'x; ('n +@ 1)}} }

(* power simplify *)
interactive power_simplify {| intro [] |} 'H :
   sequent ['ext] { 'H >- 'm IN int } -->
   sequent ['ext] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car} } -->
   sequent ['ext] { 'H >- equal{op{power{'x; 'm}; power{'x; 'n}}; power{'x; ('m +@ 'n)}} }

(* Cyclic_subgroup is a subgroup of G *)
interactive cyclic_subgroup_wf1 {| intro [] |} 'H :
   sequent ['ext] { 'H >-  isset{cyclic_subgroup{elem_in_G}} }

interactive cyclic_subgroup_wf2 {| intro[] |} 'H :
   sequent ['ext] { 'H >- subset{cyclic_subgroup{elem_in_G}; car} }

interactive cyclic_subgroup_op_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'s1; cyclic_subgroup{elem_in_G}} } -->
   sequent ['ext] { 'H >- mem{'s2; cyclic_subgroup{elem_in_G}} } -->
   sequent ['ext] { 'H >- mem{op{'s1; 's2}; cyclic_subgroup{elem_in_G}} }

interactive cyclic_subgroup_id_wf {| intro[] |} 'H :
   sequent ['ext] { 'H >- mem{id; cyclic_subgroup{elem_in_G}} }

interactive cyclic_subgroup_inv_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- mem{'s; cyclic_subgroup{elem_in_G}} } -->
   sequent ['ext] { 'H >- mem{inv{'s}; cyclic_subgroup{elem_in_G}} }
