include Czf_itt_group
include Czf_itt_group_bvd
include Czf_itt_hom
include Czf_itt_sep

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

declare ker{'h; 'g1; 'g2; x. 'f['x]}

rewrite unfold_ker : ker{'h; 'g1; 'g2; x. 'f['x]} <-->
   (hom{'g1; 'g2; x. 'f['x]} & group_bvd{'h; 'g1; sep{car{'g1}; x. mem{pair{'f['x]; id{'g2}}; eqG{'g2}}}})

topval kerSubgT : int -> tactic
topval kerLcosetT : term -> int -> tactic
topval kerRcosetT : term -> int -> tactic
topval kerNormalSubgT : int -> tactic
