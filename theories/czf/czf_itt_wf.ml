(*
 * Well-formedness judgement.
 * Rules for well-formedness are included
 * in the modules for each operator.
 *
 * We also include the "restricted" judgement,
 * which is used to define restricted separation.
 *)

include Czf_itt_set

open Itt_rfun

declare wf{'A}

declare restricted{'A}

(*
 * A proposition is well-formed if it is a small type,
 * or it is a membership judgment.
 *)
primrw unfoldWf : wf{'A} <--> small_type{'A}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform wf_df : mode[prl] :: parens :: "prec"[prec_apply] :: wf{'A} =
   slot{'A} `" wf"

(*
 * $Log$
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
