include Itt_int_ext

open Refiner.Refiner.Term
open Tactic_type.Tacticals

define unfold_nat :
   nat <--> ({x:int | 'x>=0})

declare undefined

define unfoldInd :   ind{'n; 'base; k,l. 'up['k;'l]} <-->
                     ind{'n; i,j.undefined; 'base; k,l . 'up['k;'l]}



topval natBackInductionT : term -> tactic
