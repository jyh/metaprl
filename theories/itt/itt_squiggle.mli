include Itt_equal
include Itt_struct

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Tactic_type
open Tactic_type.Tacticals
open Base_theory



val is_squiggle_term : term -> bool
val dest_squiggle : term -> term * term
val mk_squiggle_term : term -> term -> term

topval sqSubstT : term -> int -> tactic

topval squash_rewriteT : tactic

