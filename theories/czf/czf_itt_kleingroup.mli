include Czf_itt_group

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

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare klein4
declare k0
declare k1
declare k2
declare k3

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_klein4_car : car{klein4} <-->
   union{sing{k0}; union{sing{k1}; union{sing{k2}; sing{k3}}}} 
rewrite unfold_klein4_eqG : eqG{klein4} <-->
   union{sing{pair{k0; k0}}; union{sing{pair{k1; k1}}; union{sing{pair{k2; k2}}; sing{pair{k3; k3}}}}} 
rewrite unfold_klein4_op00 : op{klein4; k0; k0} <--> k0
rewrite unfold_klein4_op01 : op{klein4; k0; k1} <--> k1
rewrite unfold_klein4_op02 : op{klein4; k0; k2} <--> k2
rewrite unfold_klein4_op03 : op{klein4; k0; k3} <--> k3
rewrite unfold_klein4_op10 : op{klein4; k1; k0} <--> k1
rewrite unfold_klein4_op11 : op{klein4; k1; k1} <--> k0
rewrite unfold_klein4_op12 : op{klein4; k1; k2} <--> k3
rewrite unfold_klein4_op13 : op{klein4; k1; k3} <--> k2
rewrite unfold_klein4_op20 : op{klein4; k2; k0} <--> k2
rewrite unfold_klein4_op21 : op{klein4; k2; k1} <--> k3
rewrite unfold_klein4_op22 : op{klein4; k2; k2} <--> k0
rewrite unfold_klein4_op23 : op{klein4; k2; k3} <--> k1
rewrite unfold_klein4_op30 : op{klein4; k3; k0} <--> k3
rewrite unfold_klein4_op31 : op{klein4; k3; k1} <--> k2
rewrite unfold_klein4_op32 : op{klein4; k3; k2} <--> k1
rewrite unfold_klein4_op33 : op{klein4; k3; k3} <--> k0
rewrite unfold_klein4_id   : id{klein4} <--> k0
rewrite unfold_klein4_inv0 : inv{klein4; k0} <--> k0
rewrite unfold_klein4_inv1 : inv{klein4; k1} <--> k1
rewrite unfold_klein4_inv2 : inv{klein4; k2} <--> k2
rewrite unfold_klein4_inv3 : inv{klein4; k3} <--> k3
