(* Labels as natural numberas *)

include Itt_record_label0


open Refiner.Refiner.Term
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals


declare label[t:t]

declare eq_label[x:t,y:t]{'A;'B}

topval reduce_eq_label : conv

topval decideEqLabelT : term -> term -> tactic

topval not_eq_labelT : tactic

topval eq_labelIntroT : tactic

