(*
 * We also define a resource to prove squash stability.
 * Terms are "squash stable" if their proof can be inferred from the
 * fact that they are true.  The general form is a squash
 * proof is just:
 *     sequent [it; squash] { H >> T } -->
 *     sequent [it; it] { H >> T }
 *
 * $Log$
 * Revision 1.2  1998/04/22 22:45:14  jyh
 * *** empty log message ***
 *
 * Revision 1.1  1997/08/06 16:18:42  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 *)

include Tactic_type

open Term

open Tactic_type

(*
 * Squash property.
 * ext: extract required
 * squash: extract not needed
 *)
declare ext
declare squash

(*
 * Internal type.
 *)
type squash_data
     
(*
 * The resource itself.
 *)
resource (term * tactic, tactic, squash_data) squash_resource

(*
 * Utilities.
 *)
val squash_of_proof : tactic_arg -> tactic
val is_squash_goal : tactic_arg -> bool

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
