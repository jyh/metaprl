include Czf_itt_group
include Czf_itt_cyclic_subgroup

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

declare cyclic_group{elem_in_G}

dform cyclic_group_df : except_mode[src] :: cyclic_group{elem_in_G} =
   `"<a>"

(* axioms *)
interactive cyclic_group_wf1 {| intro [] |} 'H :
   sequent ['ext] { 'H >- isset{cyclic_group{elem_in_G}} }

interactive cyclic_group_wf2 {| intro [] |} 'H :
   sequent ['ext] { 'H >- equal{cyclic_group{elem_in_G}; car} }
