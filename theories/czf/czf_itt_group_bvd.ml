include Czf_itt_group
include Czf_itt_equiv

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

declare group_bvd{'h; 'g; 's}

dform group_bvd_df : parens :: except_mode[src] :: group_bvd{'h; 'g; 's} =
   `"group_builder(" slot{'h} `"; " slot{'g} `"; " slot{'s} `")"

(* Build a group h from group g. The underlying set of h is s;
 * the operation and equivalence relation in h are the same as
 * in g.
 *)
prim_rw unfold_group_bvd : group_bvd{'h; 'g; 's} <-->
   (group{'h} & group{'g} & isset{'s} & equal{car{'h}; 's} & (all a: set. all b: set. (mem{'a; car{'h}} => mem{'b; car{'h}} => equiv{car{'h}; eqG{'h}; op{'h; 'a; 'b}; op{'g; 'a; 'b}})) & (all a: set. all b: set. (equiv{car{'h}; eqG{'h}; 'a; 'b} => equiv{car{'g}; eqG{'g}; 'a; 'b})) & (all a: set. all b: set. (mem{'a; car{'h}} => mem{'b; car{'h}} => equiv{car{'g}; eqG{'g}; 'a; 'b} => equiv{car{'h}; eqG{'h}; 'a; 'b})))

interactive group_bvd_wf {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- "type"{group_bvd{'h; 'g; 's}} }

interactive group_bvd_intro {| intro [] |} 'H :
   sequent [squash] { 'H >- 'h IN label } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- group{'h} } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equal{car{'h}; 's} } -->
   sequent ['ext] { 'H; a: set; b: set; x: mem{'a; car{'h}}; y: mem{'b; car{'h}} >- equiv{car{'h}; eqG{'h}; op{'h; 'a; 'b}; op{'g; 'a; 'b}} } -->
   sequent ['ext] { 'H; c: set; d: set; u: equiv{car{'h}; eqG{'h}; 'c; 'd} >- equiv{car{'g}; eqG{'g}; 'c; 'd} } -->
   sequent ['ext] { 'H; p: set; q: set; x: mem{'p; car{'h}}; y: mem{'q; car{'h}}; v: equiv{car{'g}; eqG{'g}; 'p; 'q} >- equiv{car{'h}; eqG{'h}; 'p; 'q} } -->
   sequent ['ext] { 'H >- group_bvd{'h; 'g; 's} }
