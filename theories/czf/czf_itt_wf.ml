(*
 * Well-formedness judgement.
 * Rules for well-formedness are included
 * in the modules for each operator.
 *
 * We also include the "restricted" judgement,
 * which is used to define restricted separation.
 *)

include Czf_itt_set

open Refiner.Refiner.RefineErrors
open Itt_rfun

declare wf{'A}

declare restricted{'A}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform wf_df : mode[prl] :: parens :: "prec"[prec_apply] :: wf{'A} =
   slot{'A} `" wf"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * We need the property that every well-formed proposition
 * is a type.  The real proof is delayed until the theory is collected
 * and an induction form is given for well-formed formulas.
 *)
prim wf_type 'H :
   sequent ['ext] { 'H >- wf{'T} } -->
   sequent ['ext] { 'H >- "type"{'T} } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Apply the type rule.
 *)
let d_wf_typeT i p =
   if i = 0 then
      let n = Sequent.hyp_count p in
         wf_type n p
   else
      raise (RefineError ("d_wf_typeT", StringIntError ("d_wf_typeT only applies to conclusions", i)))

(*
 * $Log$
 * Revision 1.3  1998/07/01 04:37:30  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.2  1998/06/22 19:46:08  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.1  1998/06/15 22:32:55  jyh
 * Added CZF.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
