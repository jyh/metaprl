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

declare power{'g; 'z; 'n}
declare cyclic_subgroup{'g; 'a}

prim_rw unfold_power : power{'g; 'z; 'n} <-->
   ind{'n; i, j. op{'g; inv{'g; 'z}; power{'g; 'z; ('n +@ 1)}}; id{'g}; k, l. op{'g; 'z; power{'g; 'z; ('n -@ 1)}}}

prim_rw unfold_cyclic_subgroup : cyclic_subgroup{'g; 'a} <-->
   collect{int; x. power{'g; 'a; 'x}}

let fold_power = makeFoldC << power{'g; 'z; 'n} >> unfold_power
let fold_cyclic_subgroup = makeFoldC << cyclic_subgroup{'g; 'a} >> unfold_cyclic_subgroup

prec prec_power

(* prec prec_op < prec_power *)

dform power_df : parens :: "prec"[prec_power] :: except_mode[src] :: power{'g; 'z; 'n} =
   `"power(" slot{'g} `"; " slot{'z}  `"; " slot{'n} `")"

dform cyclic_subgroup_df : except_mode[src] :: cyclic_subgroup{'g; 'a} =
   `"cyclic_subgroup(" slot{'g} `"; " slot{'a} `")"

(*
 * Properties.
 *)
(* Power is a set *)
interactive power_wf1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{'z} } -->
   sequent ['ext] { 'H >- mem{'z; car{'g}} } -->
   sequent ['ext] { 'H >- isset{power{'g; 'z; 'n}} }

(* The power of an element in the carrier of a group is also in the carrier *)
interactive power_wf2 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{'z} } -->
   sequent ['ext] { 'H >- mem{'z; car{'g}} } -->
   sequent ['ext] { 'H >- mem{power{'g; 'z; 'n}; car{'g}} }

(* x ^ (n + 1) * x ^ (-1) = x ^ n *)
interactive power_property1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- equal{op{'g; power{'g; 'x; ('n +@ 1)}; inv{'g; 'x}}; power{'g; 'x; 'n}} }

(* x ^ n * x = x ^ (n + 1) *)
interactive power_property2 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- equal{op{'g; power{'g; 'x; 'n}; 'x}; power{'g; 'x; ('n +@ 1)}} }

(* Power simplify *)
interactive power_simplify {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- 'm IN int } -->
   sequent ['ext] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- equal{op{'g; power{'g; 'x; 'm}; power{'g; 'x; 'n}}; power{'g; 'x; ('m +@ 'n)}} }

(* Cyclic_subgroup is a subgroup of G *)
interactive cyclic_subgroup_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- isset{cyclic_subgroup{'g; 'a}} }

interactive cyclic_subgroup_car_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- subset{cyclic_subgroup{'g; 'a}; car{'g}} }

interactive cyclic_subgroup_op_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'s1; cyclic_subgroup{'g; 'a}} } -->
   sequent ['ext] { 'H >- mem{'s2; cyclic_subgroup{'g; 'a}} } -->
   sequent ['ext] { 'H >- mem{op{'g; 's1; 's2}; cyclic_subgroup{'g; 'a}} }

interactive cyclic_subgroup_id_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- mem{id{'g}; cyclic_subgroup{'g; 'a}} }

interactive cyclic_subgroup_inv_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- mem{'s; cyclic_subgroup{'g; 'a}} } -->
   sequent ['ext] { 'H >- mem{inv{'g; 's}; cyclic_subgroup{'g; 'a}} }
