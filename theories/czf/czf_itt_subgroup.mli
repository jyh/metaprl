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

declare subgroup{'g; 's}

rewrite unfold_subgroup : subgroup{'g; 's} <-->
   (group{'g} & group{'s} & subset{car{'s}; car{'g}} & (all a: set. all b:set. (mem{'a; car{'s}} => mem{'b; car{'s}} => equal{op{'s; 'a; 'b}; op{'g; 'a; 'b}})))

topval subgroupIsectT: term -> term -> tactic
