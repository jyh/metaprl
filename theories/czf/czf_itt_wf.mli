(*
 * Well-formedness judgement.
 * Rules for well-formedness are included
 * in the modules for each operator.
 *
 * We also include the "restricted" judgement,
 * which is used to define restricted separation.
 *)

include Czf_itt_set

open Tactic_type

declare wf{'A}

declare restricted{'A}

(*
 * We need the property that every well-formed proposition
 * is a type.  The proof is delayed until the theory is collected
 * and an induction form is given for well-formed formulas.
 *)
axiom wf_type 'H :
   sequent ['ext] { 'H >- wf{'T} } -->
   sequent ['ext] { 'H >- "type"{'T} }

(*
 * Apply the rule.
 *)
val d_wf_typeT : int -> tactic

(*
 * $Log$
 * Revision 1.2  1998/06/22 19:46:09  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.1  1998/06/15 22:32:56  jyh
 * Added CZF.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
