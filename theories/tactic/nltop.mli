(*
 * Define a resource to evaluate toplevel expressions.
 *)

open Refiner.Refiner.TermType

open Tactic_type
open Rewrite_type

(*
 * These are the values that we recognize.
 *)
type expr =
   (* Base types *)
   UnitExpr of unit
 | BoolExpr of bool
 | IntExpr of int
 | StringExpr of string
 | TermExpr of term
 | TacticExpr of tactic
 | ConvExpr of conv

   (* Uptyped tuples and functions *)
 | ListExpr of expr list
 | TupleExpr of expr list
 | FunExpr of (expr -> expr)

   (* Common cases are typed *)
 | UnitFunExpr of (unit -> expr)
 | BoolFunExpr of (bool -> expr)
 | IntFunExpr of (int -> expr)
 | StringFunExpr of (string -> expr)
 | TermFunExpr of (term -> expr)
 | TacticFunExpr of (tactic -> expr)
 | IntTacticFunExpr of ((int -> tactic) -> expr)
 | ConvFunExpr of (conv -> expr)

   (* These functions take lists *)
 | AddrFunExpr of (int list -> expr)
 | StringListFunExpr of (string list -> expr)
 | TermListFunExpr of (term list -> expr)
 | TacticListFunExpr of (tactic list -> expr)
 | ConvListFunExpr of (conv list -> expr)

(*
 * The resource maps strings to values.
 *)
type top_data
type top_table

resource (string * expr, top_table, top_data) toploop_resource

(*
 * Add a list of expressions to the toploop.
 *)
val toploop_add : toploop_resource -> (string * expr) list -> toploop_resource

(*
 * Fetch a resource by module name.
 *)
val get_resource : string -> toploop_resource

(*
 * A resource for compiling expressions from OCaml input.
 *)
val expr_of_ocaml_expr : top_table -> MLast.expr -> expr
val expr_of_ocaml_str_item : top_table -> MLast.str_item -> expr

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
