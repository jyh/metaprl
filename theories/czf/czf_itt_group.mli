include Itt_record_label0
include Czf_itt_member
include Czf_itt_eq
include Czf_itt_dall
include Czf_itt_and
include Czf_itt_equiv

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
declare car{'g}         (* The "carrier" set for the group *)
declare eqG{'g}         (* The equivalence relation for the group *)
(*declare eqG{'g; 'a; 'b} (* a and b are equivalent in the group *)*)
declare op{'g; 'a; 'b}
declare id{'g}
declare inv{'g; 'a}
(*
rewrite unfold_eqG : eqG{'g; 'a; 'b} <-->
   equiv{car{'g}; eqG{'g}; 'a; 'b}

topval fold_eqG : conv
*)
topval groupCancelLeftT : int -> tactic
topval groupCancelRightT : int -> tactic
topval uniqueInvLeftT : int -> tactic
topval uniqueInvRightT : int -> tactic
