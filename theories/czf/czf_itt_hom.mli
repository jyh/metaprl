include Czf_itt_set
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

declare hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]}

rewrite unfold_hom : hom{'g1; 'g2; 'r1; 'r2; x. 'f['x]} <-->
   (group{'g1} & group{'g2} & isset{'r1} & isset{'r2} & equiv{car{'g1}; 'r1} & equiv{car{'g2}; 'r2} & fun_set{x. 'f['x]} & "dall"{car{'g1}; a. mem{'f['a]; car{'g2}}} & (all a: set. all b: set. (mem{'a; car{'g1}} => mem{'b; car{'g1}} => equiv{car{'g2}; 'r2; 'f[op{'g1; 'a; 'b}]; op{'g2; 'f['a]; 'f['b]}})))
