(*
 * These are the declares for the terms in a Filter_summary.summary_item.
 *)

include Perv
include Nuprl_font
include Base_dform

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

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

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

(*
 * Display a simple rewrite.
 *)
dform "rewrite"[@name:s]{'redex; 'contractum; 'proof} =
   szone pushm[4]
   `"rewrite" " " slot{'name} " " slot{'redex} longleftrightarrow slot{'contractum}
   popm ezone

(*
 * A conditional rewrite requires special handling of the params.
 *)
dform "context_param"[@name:s] =
   `"context_param " slot{'name}

dform "var_param"[@name:s] =
   `"var_param " slot{'name}

dform "term_param"{'t} =
   szone pushm[4]
   `"term_param " slot{'t}
   popm ezone

dform "cond_rewrite"[@name:s]{'params; 'args; 'redex; 'contractum; 'proof} =
   szone pushm[4]
   `"rewrite" " " slot{'name} " " slot{'params} `" :" " " slot{'args}
   " " longrightarrow slot{'redex} longleftrightarrow slot{'contractum}
   popm ezone

dform "axiom"[@name:s]{'stmt; 'proof} =
   szone pushm[4]
   `"axiom" " " slot{'name} `" : : " slot{'stmt}
   popm ezone

dform "rule"[@name:s]{'params; 'stmt; 'proof} =
   szone pushm[4]
   `"axiom" " " slot{'name} " " slot{'params} `" :" " " slot{'stmt}
   ezone popm

dform "opname"[@name:s]{'term} =
   szone pushm[4]
   `"opname" " " slot{'term}
   ezone popm

dform "mlterm"{'term; 'cons; 'oexpr} =
   szone pushm[4]
   `"mlterm" " " slot{'term}
   ezone popm

dform "condition"{'term; 'cons; 'oexpr} =
   szone pushm[4]
   `"condition" " " slot{'term}
   ezone popm

(*
 * Parent path is separated by dots.
 *)
declare path{'t}

dform path{cons{."parent"[@name:s]; nil}} =
   slot{'name}

dform path{cons{."parent"[@name:s]; .cons{'n1; 'n2}}} =
   slot{'name} `"." cons{'n1; 'n2}

dform "parent"{'path; 'opens; 'resources} =
   path{'path}

(*
 * Nested module is indented.
 *)
dform "module"[@name:s]{'info} =
   szone pushm[4]
   `"module" " " slot{'name} `" = " break slot{'info}
   ezone popm

dform "dform"{'modes; 'redex; 'def} =
   szone pushm[4]
   `"dform" " " slot{'modes} slot{'redex} `" = " slot{'def}
   ezone popm

(*
 * Precedence relations.
 *)
declare "rel"{'op}

dform "rel"{."prec_rel"["lt"]} = `"<"
dform "rel"{."prec_rel"["eq"]} = `"="
dform "rel"{."prec_rel"["gt"]} = `">"

dform "prec"[@name:s] =
   `"prec" " " slot{'name}

dform "prec_rel"{'op; 'left; 'right} =
   `"prec_rel " slot{'left} "rel"{'op} slot{'right}

dform "id"{'id} =
   `"id " slot{'id}

dform "resource"[@name]{'extract; 'improve; 'data} =
   szone pushm[4]
   `"resource" " " slot{'name} `"(" pushm slot{'extract} `";" slot{'improve} `";" slot{'data} popm `")"
   popm ezone

dform "infix"[@name] =
   `"infix" " " slot{'name}

dform "magic_block"[@name:s]{'items} =
   `"magic_block" " " slot{'name} `" = " break slot{'items}

dform "summary_item"{'term} =
   slot{'term}

(*
 * $Log$
 * Revision 1.1  1998/04/17 01:31:31  jyh
 * Editor is almost constructed.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
