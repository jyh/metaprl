include Czf_itt_group
include Czf_itt_subset
include Czf_itt_isect

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals

open Base_dtactic
open Base_auto_tactic

(* subgroup{'g; 's} is a type representing the subgroup
 * of the group represented by 'g, where 's is the
 * carrier set for the specific subgroup.
 *)
declare subgroup{'g; 's}

dform subgroup_df : except_mode[src] :: subgroup{'g; 's} =
   `"subgroup(" slot{'g} `"; " slot{'s} `")"

(* Axioms *)
interactive subgroup_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- "type"{subgroup{'g; 's}} }

interactive subgroup_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- subset{'s; car{'g}} } -->
   sequent ['ext] { 'H; a: set; b: set; x: mem{'a; 's}; y: mem{'b; 's} >- mem{op{'g; 'a; 'b}; 's} } -->
   sequent ['ext] { 'H >- mem{id{'g}; 's} } -->
   sequent ['ext] { 'H; a: set; b: mem{'a; 's} >- mem{inv{'g; 'a}; 's} } -->
   sequent ['ext] { 'H >- subgroup{'g; 's} }

interactive subgroup_car_elim (*{| elim [SelectOption 1] |}*) 'H 'J :
   sequent [squash] { 'H; x: subgroup{'g; 's}; 'J['x] >- 'g IN label } -->
   sequent [squash] { 'H; x: subgroup{'g; 's}; 'J['x] >- isset{'s} } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x] >- group{'g} } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x]; y: subset{'s; car{'g}} >- 'C['x] } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x] >- 'C['x] }

interactive subgroup_op_elim (*{| elim [SelectOption 2] |}*) 'H 'J 'a 'b :
   sequent [squash] { 'H; x: subgroup{'g; 's}; 'J['x] >- 'g IN label } -->
   sequent [squash] { 'H; x: subgroup{'g; 's}; 'J['x] >- isset{'s} } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x] >- group{'g} } -->
   sequent [squash] { 'H; x: subgroup{'g; 's}; 'J['x] >- isset{'a} } -->
   sequent [squash] { 'H; x: subgroup{'g; 's}; 'J['x] >- isset{'b} } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x] >- mem{'a; 's} } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x] >- mem{'b; 's} } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x]; y: mem{op{'g; 'a; 'b}; 's} >- 'C['x] } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x] >- 'C['x] }

interactive subgroup_id_elim (*{| elim [SelectOption 3] |}*) 'H 'J :
   sequent [squash] { 'H; x: subgroup{'g; 's}; 'J['x] >- 'g IN label } -->
   sequent [squash] { 'H; x: subgroup{'g; 's}; 'J['x] >- isset{'s} } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x] >- group{'g} } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x]; y: mem{id{'g}; 's} >- 'C['x] } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x] >- 'C['x] }

interactive subgroup_inv_elim (*{| elim [SelectOption 4] |}*) 'H 'J 'a :
   sequent [squash] { 'H; x: subgroup{'g; 's}; 'J['x] >- 'g IN label } -->
   sequent [squash] { 'H; x: subgroup{'g; 's}; 'J['x] >- isset{'s} } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x] >- group{'g} } -->
   sequent [squash] { 'H; x: subgroup{'g; 's}; 'J['x] >- isset{'a} } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x] >- mem{'a; 's} } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x]; y: mem{inv{'g; 'a}; 's}  >- 'C ['x] } -->
   sequent ['ext] { 'H; x: subgroup{'g; 's}; 'J['x] >- 'C['x] }

let subgroupEliminationT n p =
   let n = if n<0 then (Sequent.hyp_count p) + n + 1 else n in
   try
      let sel = get_sel_arg p in
      let l = Sequent.get_term_list_arg p "with" in
      let i, j = Sequent.hyp_indices p n in
      match sel, l with
         1, [] ->
            (subgroup_car_elim i j) p
       | 2, [a; b] ->
            (subgroup_op_elim i j a b) p
       | 3, [] ->
            (subgroup_id_elim i j) p
       | 4, [a] ->
            (subgroup_inv_elim i j a) p
       | _ ->
            raise (RefineError ("subgroupElimination", StringError ("select option is out of range ([1,2,3,4]) or wrong number of terms")))
   with RefineError ("get_attribute",_) ->
      raise (RefineError ("subgroupElimination", StringError ("need a select option and a term list")))

let resource elim += (<<subgroup{'g; 's}>>,subgroupEliminationT)

(* Properties *)
(* The intersections of subgroups H1 and H2 of a group G is again a subgroup of G. *)
interactive subgroup_isect {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- subgroup{'g; 's1} } -->
   sequent ['ext] { 'H >- subgroup{'g; 's2} } -->
   sequent ['ext] { 'H >- subgroup{'g; ."isect"{'s1; 's2}} }
