open Tactic_type.Tacticals
open Tactic_type.Conversionals

topval unselectC : conv
topval selectC : conv
topval ifSelectedC : conv

topval unselectT : tactic
topval selectT : int -> int -> tactic
topval selectGoalT : tactic
topval selectHypT : int -> tactic
topval selectAssumT : int -> tactic

topval rws : conv -> tactic
topval selectUpT : tactic
topval selectDownT : int list -> tactic
topval selectSubAT: int -> int -> tactic
topval selectDownAT: int list -> tactic
topval selectGoalDownT : int list -> tactic
topval selectGoalDownAT: int list -> tactic
