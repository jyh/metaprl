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

declare power{'g; 'z; 'n}
declare cyclic_subgroup{'g; 'a}

rewrite unfold_power : power{'g; 'z; 'n} <-->
   ind{'n; i, j. op{'g; inv{'g; 'z}; power{'g; 'z; ('n +@ 1)}}; id{'g}; k, l. op{'g; 'z; power{'g; 'z; ('n -@ 1)}}}

rewrite unfold_cyclic_subgroup : cyclic_subgroup{'g; 'a} <-->
   collect{int; x. power{'g; 'a; 'x}}

prec prec_power

topval fold_power : conv
topval fold_cyclic_subgroup : conv
