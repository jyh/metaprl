include Czf_itt_set
include Czf_itt_member
include Czf_itt_group
include Czf_itt_equiv

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

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

declare abel{'g}

rewrite unfold_abel: abel{'g} <-->
   (group{'g} & (all a: set. all b: set. (mem{'a; car{'g}} => mem{'b; car{'g}} => equiv{car{'g}; eqG{'g}; op{'g; 'a; 'b}; op{'g; 'b; 'a}})))
