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
declare cyc_subg{'g; 's; 'a}

rewrite unfold_power : power{'g; 'z; 'n} <-->
   ind{'n; i, j. op{'g; inv{'g; 'z}; power{'g; 'z; ('n +@ 1)}}; id{'g}; k, l. op{'g; 'z; power{'g; 'z; ('n -@ 1)}}}

rewrite unfold_cyc_subg : cyc_subg{'g; 's; 'a} <-->
   (group{'g} & group{'s} & equal{car{'s}; collect{int; x. power{'g; 'a; 'x}}} & (all a: set. all b:set. (mem{'a; car{'s}} => mem{'b; car{'s}} => equal{op{'s; 'a; 'b}; op{'g; 'a; 'b}})))

prec prec_power

topval fold_power : conv
topval fold_cyc_subg : conv
topval cycsubgSubgroupT: term -> tactic
