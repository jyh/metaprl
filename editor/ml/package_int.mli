(*
 * There are three types of packages.  This is an interactive
 * package that contains interactive proofs, theorem statements, etc.
 * A package has a name, and a magic number.
 *)

include Package_type

(*
 * The package type.
 *)
type t

(*
 * Constructors.
 *)
val create : unit -> t

(*
 * Operations.
 *)
val add : t -> item -> unit
val rename : t -> string -> unit

(*
 * Listing the package.
 *)
val items_of_package : t -> item list

(*
 * IO operations.
 *)
val save : t -> unit

val restore_tactics : in_channel -> int -> Ast.expr array
val restore : in_channel -> int -> tactic_resources -> tactic array -> t

(*
 * $Log$
 * Revision 1.1  1997/08/06 16:17:18  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
