(* Labels as natural numberas *)

extends Itt_record_label0

open Refiner.Refiner.TermType
open Tactic_type.Conversionals

declare label[t:t]

declare eq_label[x:t,y:t]{'A;'B}

topval reduce_eq_label : conv

topval decideEqLabelT : term -> term -> tactic

topval not_eq_labelT : tactic

topval eq_labelIntroT : tactic

topval neq_label_elimT : int -> tactic
