include Itt_record_label0
include Czf_itt_set
include Czf_itt_member
include Czf_itt_eq
include Czf_itt_dall
include Czf_itt_and
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

declare group{'g}
declare car{'g}   (* The "carrier" set for the group *)
declare op{'g; 'a; 'b}
declare id{'g}
declare inv{'g; 'a}

prec prec_op

dform group_df : except_mode[src] :: group{'g} =
   slot{'g} `" group"

dform car_df : except_mode[src] :: car{'g} =
   `"car(" slot{'g} `")"

dform id_df : except_mode[src] :: id{'g} =
   `"id(" slot{'g} `")"

dform op_df : parens :: "prec"[prec_op] :: except_mode[src] :: op{'g; 'a; 'b} =
   `"op(" slot{'g} `"; " slot{'a}  `"; " slot{'b} `")"

dform inv_df : parens :: except_mode[src] :: inv{'g; 'a} =
   `"inv(" slot{'g} `"; " slot{'a} `")"

(*
 * axioms
 *)
interactive group_type {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- "type"{group{'g}} }

interactive car_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{car{'g}} }

interactive op_wf1 {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- isset{op{'g; 's1; 's2}} }

interactive op_wf2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- mem{op{'g; 's1; 's2}; car{'g}} }

interactive op_equiv1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; 's1; 's2} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; 's3; 's1}; op{'g; 's3; 's2}} }

interactive op_equiv2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; 's1; 's2} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}} }

interactive op_equiv_fun1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- equiv_fun_set{car{'g}; 'R; z. op{'g; 'z; 's}} }

interactive op_equiv_fun2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- equiv_fun_set{car{'g}; 'R; z. op{'g; 's; 'z}} }

interactive op_eq_fun1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- fun_set{z. op{'g; 'z; 's}} }

interactive op_eq_fun2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- fun_set{z. op{'g; 's; 'z}} }

interactive op_assoc1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; op{'g; 's1; 's2}; 's3}; op{'g; 's1; op{'g; 's2; 's3}}} }

interactive op_assoc2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; 's1; op{'g; 's2; 's3}}; op{'g; op{'g; 's1; 's2}; 's3}} }

interactive id_wf1 {| intro [] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- isset{id{'g}} }

interactive id_wf2 {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{id{'g}; car{'g}} }

interactive id_eq1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; id{'g}; 's}; 's} }

interactive id_eq2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; 's; id{'g}}; 's} }

interactive inv_wf1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- isset{inv{'g; 's1}} }

interactive inv_wf2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{inv{'g; 's1}; car{'g}} }

interactive inv_equiv_fun1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- equiv_fun_set{car{'g}; 'R; z. inv{'g; 'z}} }

interactive inv_eq_fun1 {| intro[] |} 'H :
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- fun_set{z. inv{'g; 'z}} }

interactive inv_id1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; inv{'g; 's1}; 's1}; id{'g}} }

interactive inv_id2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; 's1; inv{'g; 's1}}; id{'g}} }

(*
 * theorems
 *)

interactive equiv_op_fun1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'b; car{'g}} } -->
   sequent ['ext] { 'H >- equiv_fun_prop{car{'g}; 'R; z. equiv{car{'g}; 'R; op{'g; 'z; 'a}; op{'g; 'z; 'b}}} }

interactive equiv_op_fun2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'b; car{'g}} } -->
   sequent ['ext] { 'H >- equiv_fun_prop{car{'g}; 'R; z. equiv{car{'g}; 'R; op{'g; 'a; 'z}; op{'g; 'b; 'z}}} }

(*
(* Cancellation: a * b = a * c => b = c *)
interactive cancel1 {| intro [] |} 'H (*'g 's1*) :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; 's1; 's2}; op{'g; 's1; 's3}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; 's2; 's3} }

(* Cancellation: b * a = c * a => b = c *)
interactive cancel2 {| intro [] |} 'H 'g 's3 :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; 's1; 's2} }

let groupCancelLeftT t1 t2 p =
   cancel1 (Sequent. hyp_count_addr p) t1 t2 p

let groupCancelRightT t1 t2 p =
   cancel2 (Sequent. hyp_count_addr p) t1 t2 p
*)

(* Cancellation: a * b = a * c => b = c *)
interactive cancel1 (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- isset{'s1} } -->
   sequent [squash] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- isset{'s2} } -->
   sequent [squash] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- isset{'s3} } -->
   sequent [squash] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- isset{'R} } -->
   sequent [squash] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- 'g IN label } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- group{'g} } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's2}; op{'g; 's1; 's3}}; 'J['x] >- equiv{car{'g}; 'R; 's2; 's3} }

(* Cancellation: b * a = c * a => b = c *)
interactive cancel2 (*{| elim [] |}*) 'H 'J :
   sequent [squash] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- isset{'s1} } -->
   sequent [squash] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- isset{'s2} } -->
   sequent [squash] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- isset{'s3} } -->
   sequent [squash] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- isset{'R} } -->
   sequent [squash] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- 'g IN label } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- group{'g} } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- mem{'s1; car{'g}} } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- mem{'s3; car{'g}} } -->
   sequent ['ext] { 'H; x: equiv{car{'g}; 'R; op{'g; 's1; 's3}; op{'g; 's2; 's3}}; 'J['x] >- equiv{car{'g}; 'R; 's1; 's2} }

let groupCancelLeftT i p =
   let j, k = Sequent.hyp_indices p i in
      cancel1 j k p

let groupCancelRightT i p =
   let j, k = Sequent.hyp_indices p i in
      cancel2 j k p

(* Unique Id *)
interactive unique_id1 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'e2} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'e2; car{'g}} } -->
   sequent ['ext] { 'H >- "dall"{car{'g}; s. equiv{car{'g}; 'R; op{'g; 'e2; 's}; 's}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; 'e2; id{'g}} }

interactive unique_id2 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'e2} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'e2; car{'g}} } -->
   sequent ['ext] { 'H >- "dall"{car{'g}; s. equiv{car{'g}; 'R; op{'g; 's; 'e2}; 's}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; 'e2; id{'g}} }

interactive unique_inv1 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; 's2; 's}; id{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; 's2; inv{'g; 's}} }

interactive unique_inv2 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'s; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; 's; 's2}; id{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; 's2; inv{'g; 's}} }

(* Unique solution for a * x = b : x = a' * b *)
interactive unique_sol1 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'b; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'x; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; 'a; 'x}; 'b} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; 'x; op{'g; inv{'g; 'a}; 'b}} }

(* Unique solution for y * a = b : y = b * a' *)
interactive unique_sol2 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent [squash] { 'H >- isset{'y} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'b; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'y; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; op{'g; 'y; 'a}; 'b} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; 'y; op{'g; 'b; inv{'g; 'a}}} }

(* (a * b)' = b' * a'  *)
interactive inv_simplify {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- mem{'a; car{'g}} } -->
   sequent ['ext] { 'H >- mem{'b; car{'g}} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; inv{'g; op{'g; 'a; 'b}}; op{'g; inv{'g; 'b}; inv{'g; 'a}}} }

(* Inverse of id *)
interactive inv_of_id {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'R} } -->
   sequent [squash] { 'H >- 'g IN label } -->
   sequent ['ext] { 'H >- group{'g} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R} } -->
   sequent ['ext] { 'H >- equiv{car{'g}; 'R; inv{'g; id{'g}}; id{'g}} }
