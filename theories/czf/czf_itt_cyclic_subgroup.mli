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
declare cyc_subg{'s; 'g; 'a}

rewrite unfold_power : power{'g; 'z; 'n} <-->
   ind{'n; i, j. op{'g; inv{'g; 'z}; power{'g; 'z; ('n +@ 1)}}; id{'g}; k, l. op{'g; 'z; power{'g; 'z; ('n -@ 1)}}}

rewrite unfold_cyc_subg : cyc_subg{'s; 'g; 'a} <-->
   (group{'s} & group{'g} & mem{'a; car{'g}} & equal{car{'s}; collect{int; x. power{'g; 'a; 'x}}} & (all b: set. all c: set. (mem{'b; car{'s}} => mem{'c; car{'s}} => equiv{car{'s}; eqG{'s}; op{'s; 'b; 'c}; op{'g; 'b; 'c}})) & (all b: set. all c: set. (equiv{car{'s}; eqG{'s}; 'b; 'c} => equiv{car{'g}; eqG{'g}; 'b; 'c})) & (all b: set. all c:set. (mem{'b; car{'s}} => mem{'c; car{'s}} => equiv{car{'g}; eqG{'g}; 'b; 'c} => equiv{car{'s}; eqG{'s}; 'b; 'c})))

topval fold_power : conv
topval fold_cyc_subg : conv
topval cycsubgSubgroupT: term -> tactic
