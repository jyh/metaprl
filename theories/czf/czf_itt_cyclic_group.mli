include Czf_itt_group
include Czf_itt_cyclic_subgroup
include Czf_itt_subgroup
include Czf_itt_subset
include Itt_logic

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

declare cycgroup{'g; 'a}

rewrite unfold_cycgroup : cycgroup{'g; 'a} <-->
   cyc_subg{'g; 'g; 'a}

topval fold_cycgroup : conv
topval cycgroupAbelT: term -> tactic
