include Czf_itt_group
include Czf_itt_eq
include Czf_itt_subset
include Czf_itt_isect

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Sequent
open Tactic_type.Tacticals
open Var
open Mptop

open Base_dtactic
open Base_auto_tactic

declare subgroup{'s; 'g}

rewrite unfold_subgroup : subgroup{'s; 'g} <-->
   (group{'s} & group{'g} & subset{car{'s}; car{'g}} & (all a: set. all b: set. (mem{'a; car{'s}} => mem{'b; car{'s}} => equiv{car{'s}; eqG{'s}; op{'s; 'a; 'b}; op{'g; 'a; 'b}})) & (all a: set. all b: set. (equiv{car{'s}; eqG{'s}; 'a; 'b} => equiv{car{'g}; eqG{'g}; 'a; 'b})) & (all a: set. all b: set. (mem{'a; car{'s}} => mem{'b; car{'s}} => equiv{car{'g}; eqG{'g}; 'a; 'b} => equiv{car{'s}; eqG{'s}; 'a; 'b})))

topval subgroupIsectT: term -> term -> tactic
