extends Itt_equal
extends Itt_struct

open Basic_tactics

val is_squiggle_term : term -> bool
val dest_squiggle : term -> term * term
val mk_squiggle_term : term -> term -> term

topval sqSubstT : term -> int -> tactic
topval sqSymT : tactic

topval hypC : int -> conv
topval revHypC : int -> conv
topval assumC : int -> conv
topval revAssumC : int -> conv

