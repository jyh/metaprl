include Itt_int_ext

open Refiner.Refiner.Term
open Tactic_type.Tacticals

define unfold_nat :
   nat <--> ({x:int | 'x>=0})

topval natBackInductionT : term -> tactic
