extends Itt_int_ext

open Refiner.Refiner.Term
open Tactic_type.Tacticals
open Tactic_type.Conversionals

define unfold_nat :
   nat <--> ({x:int | 'x>=0})

define unfold_nat_plus :
   nat_plus <--> ({x:int | 'x>0})

define unfold_finite_nat : nat{'k} <--> int_seg{0; 'k}

define unfoldInd : ind{'n; 'base; k,l. 'up['k;'l]} <-->
                   ind{'n; i,j.it; 'base; k,l . 'up['k;'l]}

topval foldInd : conv

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval natBackInductionT : term -> tactic

topval positiveRule1T : tactic
topval positiveRule2T : tactic
