include Czf_itt_dall
include Czf_itt_dexists

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

declare set_bvd{'s; x. 'a['x]}             (* { a(x) | x in s } *)
declare setbvd_prop{'s; x. 'p['x]}        (* { x in s | p(x) } *)

rewrite unfold_set_bvd: set_bvd{'s; x. 'a['x]} <-->
   set_ind{'s; t, f, g. collect{'t; y. 'a['f 'y]}}

rewrite reduce_set_bvd : set_bvd{collect{'T; x. 'f['x]}; x. 'a['x]} <-->
   collect{'T; y. 'a['f['y]]}
