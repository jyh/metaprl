(*
 * We also define a resource to prove squash stability.
 * Terms are "squash stable" if their proof can be inferred from the
 * fact that they are true.  The general form is a squash
 * proof is just:
 *     sequent [it; squash] { H >> T } -->
 *     sequent [it; it] { H >> T }
 *)

include Tacticals

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

(*
 * $Log$
 * Revision 1.5  1998/07/02 18:37:54  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.4  1998/06/01 13:56:20  jyh
 * Proving twice one is two.
 *
 * Revision 1.3  1998/05/28 13:48:07  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.2  1998/04/22 22:45:14  jyh
 * *** empty log message ***
 *
 * Revision 1.1  1997/08/06 16:18:42  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
