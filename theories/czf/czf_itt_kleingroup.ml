(*! @doc{@parents} *)
include Czf_itt_group
(*! @docoff *)

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

let _ =
   show_loading "Loading Czf_itt_kleingroup%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*! @doc{@terms} *)
declare klein4
declare k0
declare k1
declare k2
declare k3
(*! @docoff *)

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * The operation for the klein 4-group.
 * @end[doc]
 *)
prim_rw unfold_klein4_car : car{klein4} <-->
   union{sing{k0}; union{sing{k1}; union{sing{k2}; sing{k3}}}} 
prim_rw unfold_klein4_eqG : eqG{klein4} <-->
   union{sing{pair{k0; k0}}; union{sing{pair{k1; k1}}; union{sing{pair{k2; k2}}; sing{pair{k3; k3}}}}} 
prim_rw unfold_klein4_op00 : op{klein4; k0; k0} <--> k0
prim_rw unfold_klein4_op01 : op{klein4; k0; k1} <--> k1
prim_rw unfold_klein4_op02 : op{klein4; k0; k2} <--> k2
prim_rw unfold_klein4_op03 : op{klein4; k0; k3} <--> k3
prim_rw unfold_klein4_op10 : op{klein4; k1; k0} <--> k1
prim_rw unfold_klein4_op11 : op{klein4; k1; k1} <--> k0
prim_rw unfold_klein4_op12 : op{klein4; k1; k2} <--> k3
prim_rw unfold_klein4_op13 : op{klein4; k1; k3} <--> k2
prim_rw unfold_klein4_op20 : op{klein4; k2; k0} <--> k2
prim_rw unfold_klein4_op21 : op{klein4; k2; k1} <--> k3
prim_rw unfold_klein4_op22 : op{klein4; k2; k2} <--> k0
prim_rw unfold_klein4_op23 : op{klein4; k2; k3} <--> k1
prim_rw unfold_klein4_op30 : op{klein4; k3; k0} <--> k3
prim_rw unfold_klein4_op31 : op{klein4; k3; k1} <--> k2
prim_rw unfold_klein4_op32 : op{klein4; k3; k2} <--> k1
prim_rw unfold_klein4_op33 : op{klein4; k3; k3} <--> k0
prim_rw unfold_klein4_id   : id{klein4} <--> k0
prim_rw unfold_klein4_inv0 : inv{klein4; k0} <--> k0
prim_rw unfold_klein4_inv1 : inv{klein4; k1} <--> k1
prim_rw unfold_klein4_inv2 : inv{klein4; k2} <--> k2
prim_rw unfold_klein4_inv3 : inv{klein4; k3} <--> k3
(*! @docoff *)

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform klein4_df : except_mode[src] :: klein4 =
   `"klein4"

dform k0_df : except_mode[src] :: k0 =
   `"k0"

dform k1_df : except_mode[src] :: k1 =
   `"k1"

dform k2_df : except_mode[src] :: k2 =
   `"k2"

dform k3_df : except_mode[src] :: k3 =
   `"k3"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Well-formedness.
 *)
interactive klein4_label {| intro [] |} 'H :
   sequent ['ext] { 'H >- klein4 IN label }

interactive k0_isset {| intro [] |} 'H :
   sequent ['ext] { 'H >- isset{k0} }

interactive k1_isset {| intro [] |} 'H :
   sequent ['ext] { 'H >- isset{k1} }

interactive k2_isset {| intro [] |} 'H :
   sequent ['ext] { 'H >- isset{k2} }

interactive k3_isset {| intro [] |} 'H :
   sequent ['ext] { 'H >- isset{k3} }

(*
 * car and eqG.
 *)
interactive car_klein0 {| intro[] |} 'H :
   sequent ['ext] { 'H >- mem{k0; car{klein4}} }

interactive car_klein1 {| intro[] |} 'H :
   sequent ['ext] { 'H >- mem{k1; car{klein4}} }

interactive car_klein2 {| intro[] |} 'H :
   sequent ['ext] { 'H >- mem{k2; car{klein4}} }

interactive car_klein3 {| intro[] |} 'H :
   sequent ['ext] { 'H >- mem{k3; car{klein4}} }

interactive eqG_klein0 {| intro[] |} 'H :
   sequent ['ext] { 'H >- mem{pair{k0; k0}; eqG{klein4}} }

interactive eqG_klein1 {| intro[] |} 'H :
   sequent ['ext] { 'H >- mem{pair{k1; k1}; eqG{klein4}} }

interactive eqG_klein2 {| intro[] |} 'H :
   sequent ['ext] { 'H >- mem{pair{k2; k2}; eqG{klein4}} }

interactive eqG_klein3 {| intro[] |} 'H :
   sequent ['ext] { 'H >- mem{pair{k3; k3}; eqG{klein4}} }

interactive car_klein0_elim {| elim [] |} 'H 'J :
   sequent [squash] { 'H; x: mem{'y; car{klein4}}; 'J['x] >- isset{'y} } -->
   sequent ['ext] { 'H; x: mem{'y; car{klein4}}; 'J['x]; z: eq{'y; k0} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; car{klein4}}; 'J['x]; z: eq{'y; k1} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; car{klein4}}; 'J['x]; z: eq{'y; k2} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; car{klein4}}; 'J['x]; z: eq{'y; k3} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; car{klein4}}; 'J['x] >- 'T['x] }

interactive eqG_klein0_elim {| elim [] |} 'H 'J :
   sequent [squash] { 'H; x: mem{'y; eqG{klein4}}; 'J['x] >- isset{'y} } -->
   sequent ['ext] { 'H; x: mem{'y; eqG{klein4}}; 'J['x]; z: eq{'y; pair{k0; k0}} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; eqG{klein4}}; 'J['x]; z: eq{'y; pair{k1; k1}} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; eqG{klein4}}; 'J['x]; z: eq{'y; pair{k2; k2}} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; eqG{klein4}}; 'J['x]; z: eq{'y; pair{k3; k3}} >- 'T['x] } -->
   sequent ['ext] { 'H; x: mem{'y; eqG{klein4}}; 'J['x] >- 'T['x] }

(*
 * Well-formedness
 *)
interactive klein4_car_wf {| intro[] |} 'H :
   sequent ['ext] { 'H >- isset{car{klein4}} }

interactive klein4_eqG_wf1 {| intro[] |} 'H :
   sequent ['ext] { 'H >- isset{eqG{klein4}} }

interactive klein4_op_wf {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- isset{op{klein4; 's1; 's2}} }

interactive klein4_id_wf1 {| intro [] |} 'H :
   sequent ['ext] { 'H >- isset{id{klein4}} }

interactive klein4_inv_wf1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- isset{inv{klein4; 's1}} }

(*
 * Verification of whether this is a group.
 *)
interactive klein4_op_eq_fun1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- fun_set{z. op{klein4; 'z; 's}} }

interactive klein4_op_eq_fun2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- fun_set{z. op{klein4; 's; 'z}} }

interactive klein4_op_eqG_fun1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- equiv_fun_set{car{klein4}; eqG{klein4}; z. op{klein4; 'z; 's}} }

interactive klein4_op_equiv_fun2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- equiv_fun_set{car{klein4}; eqG{klein4}; z. op{klein4; 's; 'z}} }

interactive klein4_op_eqG1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- mem{'s1; car{klein4}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{klein4}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{klein4}} } -->
   sequent ['ext] { 'H >- equiv{car{klein4}; eqG{klein4}; 's1; 's2} } -->
   sequent ['ext] { 'H >- equiv{car{klein4}; eqG{klein4}; op{klein4; 's3; 's1}; op{klein4; 's3; 's2}} }

interactive klein4_op_eqG2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- mem{'s1; car{klein4}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{klein4}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{klein4}} } -->
   sequent ['ext] { 'H >- equiv{car{klein4}; eqG{klein4}; 's1; 's2} } -->
   sequent ['ext] { 'H >- equiv{car{klein4}; eqG{klein4}; op{klein4; 's1; 's3}; op{klein4; 's2; 's3}} }

interactive klein4_op_closure {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- mem{'s1; car{klein4}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{klein4}} } -->
   sequent ['ext] { 'H >- mem{op{klein4; 's1; 's2}; car{klein4}} }

interactive klein4_op_assoc1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- mem{'s1; car{klein4}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{klein4}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{klein4}} } -->
   sequent ['ext] { 'H >- equiv{car{klein4}; eqG{klein4}; op{klein4; op{klein4; 's1; 's2}; 's3}; op{klein4; 's1; op{klein4; 's2; 's3}}} }

interactive klein4_op_assoc2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- isset{'s3} } -->
   sequent ['ext] { 'H >- mem{'s1; car{klein4}} } -->
   sequent ['ext] { 'H >- mem{'s2; car{klein4}} } -->
   sequent ['ext] { 'H >- mem{'s3; car{klein4}} } -->
   sequent ['ext] { 'H >- equiv{car{klein4}; eqG{klein4}; op{klein4; 's1; op{klein4; 's2; 's3}}; op{klein4; op{klein4; 's1; 's2}; 's3}} }

interactive klein4_id_wf2 {| intro[] |} 'H :
   sequent ['ext] { 'H >- mem{id{klein4}; car{klein4}} }

interactive klein4_id_eq1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- mem{'s; car{klein4}} } -->
   sequent ['ext] { 'H >- equiv{car{klein4}; eqG{klein4}; op{klein4; id{klein4}; 's}; 's} }

interactive klein4_inv_equiv_fun1 {| intro[] |} 'H :
   sequent ['ext] { 'H >- equiv_fun_set{car{klein4}; eqG{klein4}; z. inv{klein4; 'z}} }

interactive klein4_inv_eq_fun1 {| intro[] |} 'H :
   sequent ['ext] { 'H >- fun_set{z. inv{klein4; 'z}} }

interactive klein4_inv_wf2 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- mem{'s1; car{klein4}} } -->
   sequent ['ext] { 'H >- mem{inv{klein4; 's1}; car{klein4}} }

interactive klein4_inv_id1 {| intro[] |} 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- mem{'s1; car{klein4}} } -->
   sequent ['ext] { 'H >- equiv{car{klein4}; eqG{klein4}; op{klein4; inv{klein4; 's1}; 's1}; id{klein4}} }
