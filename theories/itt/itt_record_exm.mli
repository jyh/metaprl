extends Itt_record
extends Itt_fun
extends Itt_int_base

open Tactic_type.Conversionals
open Var
open Tactic_type
open Tactic_type.Tacticals
open Itt_fun

topval fold_point : conv
topval unfold_point : conv
topval unfold_semigroup : conv

topval eval_a_module : conv
