include Czf_itt_group
include Czf_itt_subgroup
include Itt_int_base

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

declare elem_in_G
declare power{'z; 'n}
declare cyclic_subgroup{elem_in_G}

rewrite unfold_power : power{'z; 'n} <-->
   ind{'n; i, j. op{inv{'z}; power{'z; ('n +@ 1)}}; id; k, l. op{'z; power{'z; ('n -@ 1)}}}

rewrite unfold_cyclic_subgroup : cyclic_subgroup{elem_in_G} <-->
   collect{int; x. power{elem_in_G; 'x}}

topval fold_power : conv
topval fold_cyclic_subgroup : conv
