include Czf_itt_group
include Czf_itt_subgroup
include Czf_itt_coset

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Sequent
open Tactic_type.Tacticals
open Var
open Mptop

open Base_dtactic
open Base_auto_tactic

(*
 * A subgroup H of a group G is normal if its left and right cosets
 * coincide, that is, if gH = Ha for all g in G.
 *)
declare normal_subg{'s; 'g}

rewrite unfold_normal_subg : normal_subg{'s; 'g} <-->
   (subgroup{'s; 'g} & (all a: set. (mem{'a; car{'g}} => equal{lcoset{'s; 'g; 'a}; rcoset{'s; 'g; 'a}})))

topval equalSubsetT : tactic
topval abelNormalSubgT : term -> int -> tactic
