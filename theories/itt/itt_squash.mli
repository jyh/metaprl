(*
 * We also define a resource to prove squash stability.
 * Terms are "squash stable" if their proof can be inferred from the
 * fact that they are true.  The general form is a squash
 * proof is just:
 *     sequent [it; squash] { H >> T } -->
 *     sequent [it; it] { H >> T }
 *)

include Tacticals
include Base_theory

open Refiner.Refiner.Term

open Sequent
open Tacticals

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
val squashT : tactic

val is_squash_goal : tactic_arg -> bool
val is_squash_sequent : term -> bool
val get_squash_arg : term -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
