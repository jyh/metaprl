include Czf_itt_group
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

declare lcoset{'h; 'g; 'a}
declare rcoset{'h; 'g; 'a}

rewrite unfold_lcoset : lcoset{'h; 'g; 'a} <-->
   set_bvd{car{'h}; x. op{'g; 'a; 'x}}

rewrite unfold_rcoset : rcoset{'h; 'g; 'a} <-->
   set_bvd{car{'h}; x. op{'g; 'x; 'a}}
