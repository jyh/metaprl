open Tactic_type.Tacticals
open Tactic_type.Conversionals

topval unselectC : conv
topval selectC : conv
topval ifSelectedC : conv
topval onSelectedC : conv -> conv
topval rws : conv -> tactic
topval selectUpC : conv
topval selectDownC : int list -> conv
