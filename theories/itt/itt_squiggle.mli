extends Itt_equal
extends Itt_struct

open Refiner.Refiner.Term
open Tactic_type.Tacticals
open Tactic_type.Conversionals

val is_squiggle_term : term -> bool
val dest_squiggle : term -> term * term
val mk_squiggle_term : term -> term -> term

topval sqSubstT : term -> int -> tactic
topval sqSymT : tactic

topval hypC : int -> conv
topval revHypC : int -> conv
topval assumC : int -> conv
topval revAssumC : int -> conv

