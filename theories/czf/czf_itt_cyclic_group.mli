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

declare cyclic_group{'a}

rewrite  unfold_cyclic_group : cyclic_group{'a} <-->
   cyclic_subgroup{'a}

topval fold_cyclic_group : conv
