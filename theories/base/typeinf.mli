(*
 * Before anything, we start the type inference resource.
 * This is mostly an incomplete type inference algorithm, but
 * it is used to perform basic inference.
 *)

include Tacticals

open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst

open Sequent
open Tacticals

(*
 * A type inference is performed in a type context,
 * which maps variables to type.
 *
 * The inference infers the type for a term in the given context,
 * or it throws the exception (TypeInfer t) for a term "t" that
 * doesn't have an inferable type.
 *)

(*
 * This is the type of the inference algorithm.
 *)
type typeinf_func = term_subst -> term -> term_subst * term

(*
 * Modular components also get a recursive instance of
 * the inference algorithm.
 *)
type typeinf_comp = typeinf_func -> typeinf_func

(*
 * This is the resource addition.
 *)
type typeinf_resource_info = term * typeinf_comp

(*
 * Internal type.
 *)
type typeinf_data

(*
 * The resource itself.
 *)
resource (typeinf_resource_info, typeinf_func, typeinf_data) typeinf_resource

(*
 * Utilities.
 *)
val typeinf_of_proof : tactic_arg -> typeinf_func

(*
 * $Log$
 * Revision 1.5  1998/07/02 18:36:54  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.4  1998/06/01 13:55:42  jyh
 * Proving twice one is two.
 *
 * Revision 1.3  1998/05/28 13:47:19  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.2  1998/04/22 22:44:32  jyh
 * *** empty log message ***
 *
 * Revision 1.1  1997/08/06 16:18:20  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
