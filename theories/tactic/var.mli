(*
 * Utilities for generating variable names.
 *)

open Sequent

(* Generate a new var different from any in the list *)
val new_var         : string -> string list -> string
val maybe_new_var   : string -> string list -> string
val maybe_new_vars  : string list -> string list -> string list

val maybe_new_vars1 : tactic_arg -> string -> string
val maybe_new_vars2 : tactic_arg -> string -> string -> string * string
val maybe_new_vars3 : tactic_arg -> string -> string -> string -> string * string * string
val maybe_new_vars4 : tactic_arg -> string -> string -> string -> string -> string * string * string * string
val maybe_new_vars5 : tactic_arg -> string -> string -> string -> string -> string -> string * string * string * string * string

val get_opt_var_arg : string -> tactic_arg -> string

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
