include Itt_equal
include Itt_struct


open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Base_theory
open Typeinf



val is_squiggle_term : term -> bool
val dest_squiggle : term -> term * term
val mk_squiggle_term : term -> term -> term


topval sqSubstT : term -> int -> tactic
