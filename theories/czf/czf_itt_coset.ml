include Czf_itt_group
include Czf_itt_subgroup
include Czf_itt_set_bvd

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
 * Let H be a subgroup of a group G. The subset aH = {ah | h in H}
 * is the left coset of H containing a, while Ha = {ha | h in H}
 * is the right coset of H containing a.
 *)
declare lcoset{'h; 'g; 'a}
declare rcoset{'h; 'g; 'a}

prim_rw unfold_lcoset : lcoset{'h; 'g; 'a} <-->
   set_bvd{car{'h}; x. op{'g; 'a; 'x}}

prim_rw unfold_rcoset : rcoset{'h; 'g; 'a} <-->
   set_bvd{car{'h}; x. op{'g; 'x; 'a}}

dform lcoset_df : parens :: except_mode[src] :: lcoset{'h; 'g; 'a} =
   `"lcoset(" slot{'h} `"; " slot{'g} `"; " slot{'a} `")"

dform rcoset_df : parens :: except_mode[src] :: rcoset{'h; 'g; 'a} =
   `"rcoset(" slot{'h} `"; " slot{'g} `"; " slot{'a} `")"

interactive lcoset_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- isset{lcoset{'h; 'g; 'a}} }

interactive rcoset_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- isset{rcoset{'h; 'g; 'a}} }

interactive lcoset_member_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'y} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g} } -->
   sequent ['ext] { 'H >- exst z: set. (mem{'z; car{'h}} => equiv{car{'g}; eqG{'g}; 'y; op{'g; 'a; 'z}}) } -->
   sequent ['ext] { 'H >- mem{'y; lcoset{'h; 'g; 'a}} }

interactive rcoset_member_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'y} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g} } -->
   sequent ['ext] { 'H >- exst z: set. (mem{'z; car{'h}} => equiv{car{'g}; eqG{'g}; 'y; op{'g; 'z; 'a}}) } -->
   sequent ['ext] { 'H >- mem{'y; rcoset{'h; 'g; 'a}} }

interactive lcoset_member_elim {| elim [] |} 'H 'J :
   sequent [squash] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- 'h IN label } -->
   sequent [squash] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- 'g IN label } -->
   sequent [squash] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- isset{'a} } -->
   sequent [squash] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- isset{'y} } -->
   sequent ['ext] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- subgroup{'h; 'g} } -->
   sequent ['ext] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x]; z: set; u: mem{'z; car{'h}}; v: equiv{car{'g}; eqG{'g}; 'y; op{'g; 'a; 'z}} >- 'C['x] } -->
   sequent ['ext] { 'H; x: mem{'y; lcoset{'h; 'g; 'a}}; 'J['x] >- 'C['x] }

interactive rcoset_member_elim {| elim [] |} 'H 'J :
   sequent [squash] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- 'h IN label } -->
   sequent [squash] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- 'g IN label } -->
   sequent [squash] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- isset{'a} } -->
   sequent [squash] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- isset{'y} } -->
   sequent ['ext] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- subgroup{'h; 'g} } -->
   sequent ['ext] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x]; z: set; u: mem{'z; car{'h}}; v: equiv{car{'g}; eqG{'g}; 'y; op{'g; 'z; 'a}} >- 'C['x] } -->
   sequent ['ext] { 'H; x: mem{'y; rcoset{'h; 'g; 'a}}; 'J['x] >- 'C['x] }

interactive lcoset_subset {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g} } -->
   sequent ['ext] { 'H >- subset{lcoset{'h; 'g; 'a}; car{'g}} }

interactive rcoset_subset {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- subgroup{'h; 'g} } -->
   sequent ['ext] { 'H >- subset{rcoset{'h; 'g; 'a}; car{'g}} }
