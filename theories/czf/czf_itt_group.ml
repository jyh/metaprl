include Czf_itt_set
include Czf_itt_member
include Czf_itt_eq
include Czf_itt_dall
include Czf_itt_and

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

declare car   (* The "carrier" set for the group *)
declare op{'s1; 's2}
declare id
declare inv{'s}

dform car_df : except_mode[src] :: car =
   `"S"

dform id_df : except_mode[src] :: id =
   `"e"

dform op_df : parens :: except_mode[src] :: op{'s1; 's2} =
   slot["le"]{'s1} `" * " slot["le"]{'s2}

dform inv_df : parens :: except_mode[src] :: inv{'s} =
   slot["le"]{'s} `"'"

(* axioms *)
interactive car_wf {| intro[] |} 'H :
   sequent ['ext] { 'H >- isset{car} }

interactive op_wf1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- isset{op{'s1; 's2}} }

interactive op_wf2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'s1; car} } -->
   sequent ['ext] { 'H >- mem{'s2; car} } -->
   sequent ['ext] { 'H >- mem{op{'s1; 's2}; car} }

interactive op_eq1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} }  -->
   sequent ['ext] { 'H >- eq{op{'s3; 's1}; op{'s3; 's2}} }

interactive op_eq2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} }  -->
   sequent ['ext] { 'H >- eq{op{'s1; 's3}; op{'s2; 's3}} }

interactive op_fun1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- fun_set{z. op{'z; 's}} }

interactive op_fun2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- fun_set{z. op{'s; 'z}} }

(* interactive op_fun3 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- fun_set{z. op{'s1; 's2}} }
*)
interactive op_assoc1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- mem{'s1; car} } -->
   sequent ['ext] { 'H >- mem{'s2; car} } -->
   sequent ['ext] { 'H >- mem{'s3; car} } -->
   sequent ['ext] { 'H >- equal{op{op{'s1; 's2}; 's3}; op{'s1; op{'s2; 's3}}} }

(* let op_assoc1T p =
      op_assoc1 (Sequent.hyp_count_addr p) p *)

interactive op_assoc2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- mem{'s1; car} } -->
   sequent ['ext] { 'H >- mem{'s2; car} } -->
   sequent ['ext] { 'H >- mem{'s3; car} } -->
   sequent ['ext] { 'H >- equal{op{'s1; op{'s2; 's3}}; op{op{'s1; 's2}; 's3}} }

(* let op_assoc2T p =
      op_assoc2 (Sequent.hyp_count_addr p) p *)

interactive id_wf1 {| intro [] |} 'H :
   sequent ['ext] { 'H >- isset{id} }

interactive id_wf2 {| intro[] |} 'H :
   sequent ['ext] { 'H >- mem{id; car} }

(* interactive id_wf3 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{id} }
*)
interactive id_eq1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- mem{'s; car} } -->
   sequent ['ext] { 'H >- equal{op{id; 's}; 's} }

interactive id_eq2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- mem{'s; car} } -->
   sequent ['ext] { 'H >- equal{op{'s; id}; 's} }

let id_elim2T p =
   id_eq1 (Sequent. hyp_count_addr p) p

interactive inv_wf1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- mem{'s1; car} } -->
   sequent ['ext] { 'H >- isset{inv{'s1}} }

interactive inv_wf2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- mem{'s1; car} } -->
   sequent ['ext] { 'H >- mem{inv{'s1}; car} }

interactive inv_id1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- mem{'s1; car} } -->
   sequent ['ext] { 'H >- equal{op{inv{'s1}; 's1}; id} }

interactive inv_id2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- mem{'s1; car} } -->
   sequent ['ext] { 'H >- equal{op{'s1; inv{'s1}}; id} }

(* theorems *)
(* Cancellation: a * b = a * c => b = c *)
interactive cancelLeft {| intro [] |} 'H 's1 :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- mem{'s1; car} } -->
   sequent ['ext] { 'H >- mem{'s2; car} } -->
   sequent ['ext] { 'H >- mem{'s3; car} } -->
   sequent ['ext] { 'H >- equal{op{'s1; 's2}; op{'s1; 's3}} } -->
   sequent ['ext] { 'H >- equal{'s2; 's3} }

(* Cancellation: b * a = c * a => b = c *)
interactive cancelRight {| intro [] |} 'H 's3 :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- mem{'s1; car} } -->
   sequent ['ext] { 'H >- mem{'s2; car} } -->
   sequent ['ext] { 'H >- mem{'s3; car} } -->
   sequent ['ext] { 'H >- equal{op{'s1; 's3}; op{'s2; 's3}} } -->
   sequent ['ext] { 'H >- equal{'s1; 's2} }

let groupCancelLeftT t p =
   cancelLeft (Sequent. hyp_count_addr p) t p

let groupCancelRightT t p =
   cancelRight (Sequent. hyp_count_addr p) t p

(* Unique Id *)
interactive unique_id1 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'e2} } -->
   sequent ['ext] { 'H >- mem{'e2; car} } -->
   sequent ['ext] { 'H; x: "dall"{car; s. "and"{eq{op{'e2; 's}; 's}; eq{op{'s; 'e2}; 's}}} >- eq{'e2; id} }

(* Unique Inverse *)
interactive unique_inv {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'s; car} } -->
   sequent ['ext] { 'H >- mem{'s2; car} } -->
   sequent ['ext] { 'H; x: equal{op{'s2; 's}; id}; y: equal{op{'s; 's2}; id} >- equal{'s2; inv{'s}} }

(* Unique solution for a * x = b : x = a' * b *)
interactive unique_sol1 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent [squash] { 'H >- isset{'x} } -->
   sequent ['ext] { 'H >- mem{'a; car} } -->
   sequent ['ext] { 'H >- mem{'b; car} } -->
   sequent ['ext] { 'H >- mem{'x; car} } -->
   sequent ['ext] { 'H >- equal{op{'a; 'x}; 'b} } -->
   sequent ['ext] { 'H >- equal{'x; op{inv{'a}; 'b}} }

(* Unique solution for y * a = b : y = b * a' *)
interactive unique_sol2 {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent [squash] { 'H >- isset{'y} } -->
   sequent ['ext] { 'H >- mem{'a; car} } -->
   sequent ['ext] { 'H >- mem{'b; car} } -->
   sequent ['ext] { 'H >- mem{'y; car} } -->
   sequent ['ext] { 'H >- equal{op{'y; 'a}; 'b} } -->
   sequent ['ext] { 'H >- equal{'y; op{'b; inv{'a}}} }

(* (a * b)' = b' * a'  *)
interactive inv_simplify {| intro [] |} 'H :
   sequent [squash] { 'H >- isset{'a} } -->
   sequent [squash] { 'H >- isset{'b} } -->
   sequent ['ext] { 'H >- mem{'a; car} } -->
   sequent ['ext] { 'H >- mem{'b; car} } -->
   sequent ['ext] { 'H >- equal{inv{op{'a; 'b}}; op{inv{'b}; inv{'a}}} }
