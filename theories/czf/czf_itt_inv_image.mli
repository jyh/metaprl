include Czf_itt_set
include Czf_itt_set_bvd

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

declare inv_image{'s; x. 'a['x]; 't}  (* { x in s | a(x) in t } *)

rewrite unfold_inv_image: inv_image{'s; x. 'a['x]; 't} <-->
   setbvd_prop{'s; x. mem{'a['x]; 't}}

topval fold_inv_image : conv
