include Czf_itt_set
include Czf_itt_member
include Czf_itt_pair

open Itt_equal

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

open Itt_equal
open Itt_rfun
open Itt_struct

open Czf_itt_set

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare equiv{'s; 'r; 'a; 'b}
declare equiv{'s; 'r}

rewrite unfold_equiv : equiv{'s; 'r; 'a; 'b} <-->
   (((isset{'s} & isset{'r} & isset{'a} & isset{'b}) & mem{'a; 's} & mem{'b; 's}) & mem{pair{'a; 'b}; 'r})

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_equiv_term : term -> bool
val mk_equiv_term : term -> term -> term -> term -> term
val dest_equiv : term -> term * term * term * term

topval equivSymT : int -> tactic
topval equivTransT : term -> int -> tactic

topval equivSubstT : term -> int -> tactic
