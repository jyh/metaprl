include Czf_itt_group
include Czf_itt_equiv
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
declare cyc_subg{'s; 'g; 'a}

prim_rw unfold_power : power{'g; 'z; 'n} <-->
   ind{'n; i, j. op{'g; inv{'g; 'z}; power{'g; 'z; ('n +@ 1)}}; id{'g}; k, l. op{'g; 'z; power{'g; 'z; ('n -@ 1)}}}

prim_rw unfold_cyc_subg : cyc_subg{'s; 'g; 'a} <-->
   (group{'s} & group{'g} & mem{'a; car{'g}} & equal{car{'s}; collect{int; x. power{'g; 'a; 'x}}} & (all a: set. all b:set. (mem{'a; car{'s}} => mem{'b; car{'s}} => equal{op{'s; 'a; 'b}; op{'g; 'a; 'b}})) & (all a: set. all b: set. (equiv{car{'s}; eqG{'s}; 'a; 'b} => equiv{car{'g}; eqG{'g}; 'a; 'b})))

let fold_power = makeFoldC << power{'g; 'z; 'n} >> unfold_power
let fold_cyc_subg = makeFoldC << cyc_subg{'s; 'g; 'a} >> unfold_cyc_subg

dform power_df : parens :: except_mode[src] :: power{'g; 'z; 'n} =
   `"power(" slot{'g} `"; " slot{'z}  `"; " slot{'n} `")"

dform cyc_subg_df : except_mode[src] :: cyc_subg{'s; 'g; 'a} =
   `"cyclic_subgroup(" slot{'s} `"; " slot{'g} `"; " slot{'a} `")"

(*
 * Properties.
 *)
(* Power is a set *)
interactive power_wf1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'z} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- isset{power{'g; 'z; 'n}} }

(* The power of an element in the carrier of a group is also in the carrier *)
interactive power_wf2 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent [squash] { 'H >- isset{'z} } -->
   sequent ['ext] { 'H >- mem{'z; car{'g}} } -->
   sequent ['ext] { 'H >- mem{power{'g; 'z; 'n}; car{'g}} }

interactive power_fun {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- fun_set{z. 'f['z]} } -->
   sequent ['ext] { 'H; z: set >- mem{'f['z]; car{'g}} } -->
   sequent ['ext] { 'H >- fun_set{z. power{'g; 'f['z]; 'n}} }

interactive power_equiv_fun {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- equiv_fun_set{car{'g}; eqG{'g}; z. 'f['z]} } -->
   sequent ['ext] { 'H >- equiv_fun_set{car{'g}; eqG{'g}; z. power{'g; 'f['z]; 'n}} }

interactive power_equiv_fun1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent ['ext] { 'H >- equiv_fun_set{car{'g}; eqG{'g}; z. power{'g; 'z; 'n}} }

(* x ^ (n + 1) * x ^ (-1) = x ^ n *)
interactive power_property1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; eqG{'g}; op{'g; power{'g; 'x; ('n +@ 1)}; inv{'g; 'x}}; power{'g; 'x; 'n}} }

(* x ^ n * x = x ^ (n + 1) *)
interactive power_property2 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; eqG{'g}; op{'g; power{'g; 'x; 'n}; 'x}; power{'g; 'x; ('n +@ 1)}} }

(* Power simplify *)
interactive power_simplify {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- 'm IN int } -->
   sequent [squash] { 'H >- 'n IN int } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; eqG{'g}; op{'g; power{'g; 'x; 'm}; power{'g; 'x; 'n}}; power{'g; 'x; ('m +@ 'n)}} }

(* cyc_subg is a subgroup of G *)
interactive cyc_subg_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- "type"{cyc_subg{'s; 'g; 'a}} }

interactive cyc_subg_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- group{'s} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- equal{car{'s}; collect{int; x. power{'g; 'a; 'x}}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: mem{'a; car{'s}}; y: mem{'b; car{'s}} >- equal{op{'s; 'a; 'b}; op{'g; 'a; 'b}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: equiv{car{'s}; eqG{'s}; 'a; 'b} >- equiv{car{'g}; eqG{'g}; 'a; 'b} } -->
   sequent ['ext] { 'H >- cyc_subg{'s; 'g; 'a} }

interactive cyc_subg_subgroup 'H 'a :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- 's IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- group{'s} } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- cyc_subg{'s; 'g; 'a} } -->
   sequent ['ext] { 'H >- subgroup{'s; 'g} }

let cycsubgSubgroupT t p =
   cyc_subg_subgroup (hyp_count_addr p) t p
