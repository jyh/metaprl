(*
 * These are the declares for the terms in a Filter_summary.summary_item.
 *)

include Perv
include Nuprl_font
include Base_dform
include Ocaml_df

declare "interface"{'intf}
declare "implementation"{'impl}
declare "location"[@start:n, @finish:n]{'body}

declare "rewrite"[@name:s]{'redex; 'contractum; 'proof}
declare "cond_rewrite"[@name:s]{'params; 'args; 'redex; 'contractum; 'proof}
declare "axiom"[@name:s]{'stmt; 'proof}
declare "rule"[@name:s]{'params; 'stmt; 'proof}
declare "opname"[@name:s]{'term}
declare "mlterm"{'term; 'cons; 'oexpr}
declare "condition"{'term; 'cons; 'oexpr}
declare "parent"{'path; 'opens; 'resources}
declare "module"[@name:s]{'info}
declare "dform"{'modes; 'redex; 'def}
declare "prec"[@name:s]
declare "prec_rel"{'op; 'left; 'right}
declare "id"{'id}
declare "resource"[@name:s]{'extract; 'improve; 'data}
declare "infix"[@name:s]
declare "magic_block"[@name:s]{'items}
declare "summary_item"{'term}

declare "inherit_df"
declare "prec_df"[@name:s]
declare "parens_df"
declare "mode_df"[@mode:s]

declare "df_none"
declare "df_term"{'t}
declare "df_ml"[@printer:s, @buffer:s]{'contracta; 'code}

declare "none"
declare "some"{'t}

declare "meta_theory"{'A}
declare "meta_theorem"{'A}
declare "meta_implies"{'A; 'B}
declare "meta_function"{'A; x. 'B['x]}
declare "meta_iff"{'A; 'B}

declare "context_param"[@name:s]
declare "var_param"[@name:s]
declare "term_param"{'t}

(* Proofs *)
declare "interactive"{'t}

declare "status_bad"
declare "status_partial"
declare "status_asserted"
declare "status_complete"

declare "proof_step"{'goal; 'subgoals; 'ast; 'text}
declare "proof_node"{'proof}

declare "proof_child_goal"{'goal}
declare "proof_child_proof"{'proof}

declare "proof_aterm"{'goal; 'label; 'args}

declare "proof_var_args"{'args}
declare "proof_term_args"{'args}
declare "proof_type_arg"{'arg}
declare "proof_int_args"{'args}
declare "proof_thin"
declare "proof_dont_thin"
declare "proof_subst_arg"{'args}

(*
 * $Log$
 * Revision 1.4  1998/06/15 22:32:41  jyh
 * Added CZF.
 *
 * Revision 1.3  1998/04/29 14:48:40  jyh
 * Added ocaml_sos.
 *
 * Revision 1.2  1998/04/28 18:31:00  jyh
 * ls() works, adding display.
 *
 * Revision 1.1  1998/04/17 01:31:33  jyh
 * Editor is almost constructed.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
