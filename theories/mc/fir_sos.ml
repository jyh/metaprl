(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Operational semantics / judgements for FIR programs.
 *)

include Base_theory

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Evaluation judgement. *)
declare evals_to{ 'expr1; 'expr2 }

(* Evaluation term. *)
declare eval{ 'state; 'expr }

(* Value judgement. *)
declare value{ 'state; 'atom }

(* Non-value. *)
declare dot

(*************************************************************************
 * Display forms.
 *************************************************************************)

dform evals_to_df : except_mode[src] :: evals_to{ 'expr1; 'expr2 } =
   slot{'expr1} Nuprl_font!downarrow slot{'expr2}

dform eval_df : except_mode[src] :: eval{ 'state; 'expr } =
   `"eval(" slot{'state} `", " slot{'expr} `")"

dform value_df : except_mode[src] :: value{ 'state; 'atom } =
   `"value(" slot{'state} `", " slot{'atom} `")"

dform dot_df : except_mode[src] :: dot =
   Nuprl_font!cdot
