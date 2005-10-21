open Refiner.Refiner.Refine
open Tactic_type.Conversionals

topval fold_Poly : conv
topval atIndC : conv -> conv
topval atIndArgC : conv -> conv
topval atTermC : term -> conv -> conv
topval atTermHC : term -> conv -> conv

topval stepT : term -> term -> term -> int -> tactic
topval convT : term -> term -> term list -> int -> tactic
topval stdT : term -> term list -> int -> tactic
