include Itt_record_label0
include Czf_itt_set
include Czf_itt_member
include Czf_itt_eq
include Czf_itt_dall
include Czf_itt_and

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

declare group{'g}
declare car{'g}   (* The "carrier" set for the group *)
declare op{'g; 'a; 'b}
declare id{'g}
declare inv{'g; 'a}
(*declare eqElem{'s; 'a; 'b}*)

prec prec_op

topval groupCancelLeftT : int -> tactic
topval groupCancelRightT : int -> tactic
(*topval groupCancelLeftT : term -> term -> tactic
topval groupCancelRightT : term -> term -> tactic*)
