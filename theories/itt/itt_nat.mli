extends Itt_int_ext

open Refiner.Refiner.Term
open Tactic_type.Tacticals

define unfold_nat :
   nat <--> ({x:int | 'x>=0})

define unfoldInd : ind{'n; 'base; k,l. 'up['k;'l]} <-->
                   ind{'n; i,j.it; 'base; k,l . 'up['k;'l]}



topval natBackInductionT : term -> tactic
