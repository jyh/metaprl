extends Itt_bool
extends Itt_fun
extends Itt_esquash
extends Itt_quotient
extends Itt_logic

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Mp_resource

open Var
open Tactic_type.Tacticals
open Tactic_type.Conversionals

topval colEqSymT : tactic
topval colEqTransT : term -> tactic

topval fold_col : conv
topval fold_col_member : conv
topval fold_Col : conv
topval fold_add : conv
