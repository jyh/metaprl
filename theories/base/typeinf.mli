(*
 * Before anything, we start the type inference resource.
 * This is mostly an incomplete type inference algorithm, but
 * it is used to perform basic inference.
 *
 * $Log$
 * Revision 1.2  1998/04/22 22:44:32  jyh
 * *** empty log message ***
 *
 * Revision 1.1  1997/08/06 16:18:20  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 *)

include Tactic_type

open Term

open Tactic_type

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
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
