(*
 * These are the declares for the terms in a Filter_summary.summary_item.
 *)

include Perv
include Nuprl_font
include Base_dform
include Ocaml_df

open Printf
open Debug

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Summary%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

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

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

(*
 * Modes.
 *)
declare dform_modes{'l}

dform dform_modes_df1 : dform_modes{cons{'hd; 'tl}} =
   slot{'hd} " " `"::" space dform_modes{dform_modes; 'tl}

dform dform_modes_df2 : dform_modes{dform_modes; cons{'hd; 'tl}} =
   slot{'hd} " " `"::" space dform_modes{dform_modes; 'tl}

dform dform_modes_df3 : dform_modes{nil} =
   `""

dform dform_modes_df3 : dform_modes{dform_modes; nil} =
   hspace

(*
 * Space the items.
 *)
declare space_list{'l}

dform space_list_df1 : space_list{cons{'hd; 'tl}} =
   slot{'hd} " " space_list{'tl}

dform space_list_df2 : space_list{nil} =
   `""

(*
 * Interface just declares it.
 *)
declare lines{'e}

dform lines_nil_df : lines{nil} = `""

dform lines_cons_df : lines{cons{'e1; 'e2}} =
   szone slot{'e1} ezone newline lines{'e2}

dform interface_df : "interface"{'body} =
   szone pushm[0] pushm[4]
   `"Interface:" newline
   lines{'body} popm newline
   `"end"
   popm ezone

dform implementation_df : "implementation"{'body} =
   szone pushm[0] pushm[4]
   `"Implementation:" newline
   lines{'body} popm newline
   `"end"
   popm ezone

dform location_df : "location"[@start:n, @finish:n]{'body} =
   slot{'body}

(*
 * Display a simple rewrite.
 *)
dform rewrite_df : "rewrite"[@name:s]{'redex; 'contractum; 'proof} =
   szone pushm[4]
   slot{'proof} `" rewrite" " " slot[@name:s] " " slot{'redex} " " longleftrightarrow hspace slot{'contractum}
   popm ezone

(*
 * A conditional rewrite requires special handling of the params.
 *)
dform context_param_df : "context_param"[@name:s] =
   slot[@name:s]

dform var_param_df : "var_param"[@name:s] =
   slot[@name:s]

dform term_param_df : "term_param"{'t} =
   szone pushm[4]
   slot{'t}
   popm ezone

dform cond_rewrite_df : "cond_rewrite"[@name:s]{'params; 'args; 'redex; 'contractum; 'proof} =
   szone pushm[4]
   slot{'proof} `" rewrite" " " slot[@name:s] " " slot{'params} `" :" " " slot{'args}
   " " longrightarrow slot{'redex} longleftrightarrow slot{'contractum}
   popm ezone

dform axiom_df : "axiom"[@name:s]{'stmt; 'proof} =
   szone pushm[4]
   slot{'proof} `" axiom" " " slot[@name:s] `" : : " slot{'stmt}
   popm ezone

dform rule_df : "rule"[@name:s]{'params; 'stmt; 'proof} =
   szone pushm[4]
   slot{'proof} `" axiom" " " slot[@name:s] " " space_list{'params} `":" hspace slot{'stmt}
   ezone popm

dform opname_df : "opname"[@name:s]{'term} =
   szone pushm[4]
   `"declare" " " slot["raw"]{'term}
   ezone popm

dform mlterm_df : "mlterm"{'term; 'cons; 'oexpr} =
   szone pushm[4]
   `"mlterm" " " slot{'term}
   ezone popm

dform condition_df : "condition"{'term; 'cons; 'oexpr} =
   szone pushm[4]
   `"condition" " " slot{'term}
   ezone popm

(*
 * Parent path is separated by dots.
 *)
declare path{'t}

dform path_parent_nil_df : path{cons{."parent"[@name:s]; nil}} =
   slot[@name:s]

dform path_parent_cons_df : path{cons{."parent"[@name:s]; .cons{'n1; 'n2}}} =
   slot[@name:s] `"." cons{'n1; 'n2}

dform parent_df : "parent"{'path; 'opens; 'resources} =
   `"include" " " path{'path}

(*
 * Nested module is indented.
 *)
dform module_df : "module"[@name:s]{'info} =
   szone pushm[4]
   `"module" " " slot[@name:s] `" = " break slot{'info}
   ezone popm

dform dform_df : "dform"[@name:s]{'modes; 'redex; 'def} =
   szone pushm[4]
   `"dform" " " slot[@name:s]
   space `": " dform_modes{'modes} slot["raw"]{'redex}
   space `"=" hspace pushm slot{'def} popm
   ezone popm

(*
 * Precedence relations.
 *)
declare "rel"{'op}

dform rel_lt_df : "rel"{."prec_rel"["lt"]} = `"<"
dform rel_eq_df : "rel"{."prec_rel"["eq"]} = `"="
dform rel_gt_df : "rel"{."prec_rel"["gt"]} = `">"

dform prec_df : "prec"[@name:s] =
   `"prec" " " slot[@name:s]

dform prec_rel_df : "prec_rel"{'op; 'left; 'right} =
   `"prec_rel " slot{'left} "rel"{'op} slot{'right}

dform id_df : "id"{'id} =
   `"id " slot{'id}

dform resource_df : "resource"[@name]{'extract; 'improve; 'data} =
   szone pushm[4]
   `"resource" " " slot[@name:s] `"(" pushm slot{'extract} `";" slot{'improve} `";" slot{'data} popm `")"
   popm ezone

dform infix_df : "infix"[@name] =
   `"infix" " " slot[@name:s]

dform magic_block_df : "magic_block"[@name:s]{'items} =
   `"magic_block" " " slot[@name:s] `" =" space slot{'items}

dform summary_item_df : "summary_item"{'term} =
   slot{'term}

dform df_term_df : df_term{'t} =
   slot{'t}

dform meta_theorem_df : meta_theorem{'A} =
   slot{'A}

dform meta_implies_df : meta_implies{'A; 'B} =
   slot{'A} " " longrightarrow hspace slot{'B}

dform mode_df : mode_df[@s:s] =
   `"mode[" slot[@s:s] `"]"

dform prec_df : prec_df[@s:s] =
   `"prec[" slot[@s:s] `"]"

dform parens_df : parens_df =
   `"parens"

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
