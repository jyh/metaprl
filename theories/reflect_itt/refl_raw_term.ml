(*
 * Define terms.
 *)

include Itt_theory

include Refl_var

open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Conversionals
open Var

open Base_dtactic

open Itt_equal
open Itt_struct

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Parts of terms.
 *)
declare operator_type
declare eq_op{'op1; 'op2}

declare bterm{'sl; 't}
declare bterm_term{'bt}
declare raw_bterm_type{'T}

declare bvar{'v; 'terms}
declare bvar_type{'T}

declare term{'op; 'bterms}
declare raw_term_type

declare match_term{'t; v, tl. 'bvar_case['v; 'tl]; op, bterms. 'term_case['op; 'bterms]}
declare match_bterm{'bterm; sl, t. 'body['sl; 't]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_eq_op
prec prec_match_term

dform operator_type_df : mode[prl] :: operator_type =
   `"Operator"

dform eq_op_df : mode[prl] :: parens :: "prec"[prec_eq_op] :: eq_op{'op1; 'op2} =
   slot{'op1} `" =" space slot{'op2}

dform bterm_df1 : mode[prl] :: bterm{nil; 't} =
   slot{'t}

dform bterm_df2 : mode[prl] :: bterm{cons{'s; nil}; 't} =
   slot{'s} `"." space slot{'t}

dform bterm_df3 : mode[prl] :: bterm{cons{'s; 'sl}; 't} =
   slot{'s} `", " bterm{'sl; 't}

dform bterm_term_df : mode[prl] :: bterm_term{'t} =
   `"bterm_term(" slot{'t} `")"

dform raw_bterm_type_df : mode[prl] :: raw_bterm_type{'T} =
   `"Bterm(" slot{'T} `")"

dform bvar_df1 : mode[prl] :: bvar{'v; 'tl} =
   slot{'v} slot{'tl}

dform bvar_type_df : mode[prl] :: bvar_type{'T} =
   `"BVar(" slot{'T} `")"

dform term_df1 : mode[prl] :: term{'op; nil} =
   slot{'op}

declare curlylist{'l}

dform term_df2 : mode[prl] :: term{'op; cons{'t; 'tl}} =
   szone slot{'op} `"{" pushm[0] curlylist{cons{'t; 'tl}} `"}" popm ezone

dform term_df3 : mode[prl] :: term{'op; 'bterms} =
   slot{'op} `"{" slot{'bterms} `"}"

dform curlylist_df1 : mode[prl] :: curlylist{cons{'t; nil}} =
   slot{'t}

dform curlylist_df2 : mode[prl] :: curlylist{cons{'t; 'tl}} =
   slot{'t} `";" hspace curlylist{'tl}

dform curlylist_df3 : mode[prl] :: curlylist{'t} =
   `"{" slot{'t} `"}"

dform raw_term_type_df : mode[prl] :: raw_term_type =
   `"Term"

dform match_term_df : mode[prl] :: parens :: "prec"[prec_match_term] ::
   match_term{'t; v, tl. 'bvar_case; op, bterms. 'term_case} =
   szone pushm[1] pushm[3] `"match " slot{'t} `" with" hspace
      `"bvar(" slot{'v} `", " slot{'tl} `") ->" hspace
      slot{'bvar_case} popm hspace
   pushm[2] `"| term(" slot{'op} `", " slot{'bterms} `") ->" hspace
      slot{'term_case} popm popm ezone

dform match_bterm_df : mode[prl] :: parens :: "prec"[prec_match_term] ::
   match_bterm{'bterm; sl, t. 'body} =
   szone pushm[1] `"match " slot{'bterm} `" with" hspace
      `"bterm(" slot{'sl} `", " slot{'t} `") ->" hspace
      slot{'body}
   popm ezone

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

prim_rw unfold_bterm : bterm{'sl; 't} <--> pair{'sl; 't}
prim_rw unfold_bterm_term : bterm_term{'t} <--> snd{'t}
prim_rw unfold_raw_bterm_type : raw_bterm_type{'T} <--> (list{var_type} * 'T)
prim_rw unfold_bvar : bvar{'v; 'tl} <--> inl{pair{'v; 'tl}}
prim_rw unfold_bvar_type : bvar_type{'T} <--> (var_type * list{'T})
prim_rw unfold_term : term{'op; 'bterms} <--> inr{pair{'op; 'bterms}}
prim_rw unfold_raw_term_type : raw_term_type <--> srec{T. bvar_type{'T} + (operator_type * list{raw_bterm_type{'T}})}

prim_rw unfold_match_term : match_term{'t; v, tl. 'bvar_case['v; 'tl]; op, bterms. 'term_case['op; 'bterms]} <-->
   decide{'t; x. spread{'x; y, z. 'bvar_case['y; 'z]};
              x. spread{'x; y, z. 'term_case['y; 'z]}}

prim_rw unfold_match_bterm : match_bterm{'t; sl, t. 'body['sl; 't]} <-->
   spread{'t; sl, t. 'body['sl; 't]}

let fold_bterm = makeFoldC << bterm{'sl; 't} >> unfold_bterm
let fold_bterm_term = makeFoldC << bterm_term{'t} >> unfold_bterm_term
let fold_raw_bterm_type = makeFoldC << raw_bterm_type{'T} >> unfold_raw_bterm_type
let fold_bvar = makeFoldC << bvar{'v; 'tl} >> unfold_bvar
let fold_bvar_type = makeFoldC << bvar_type{'T} >> unfold_bvar_type
let fold_term = makeFoldC << term{'op; 'bterms} >> unfold_term
let fold_raw_term_type = makeFoldC << raw_term_type >> unfold_raw_term_type
let fold_match_term = makeFoldC << match_term{'t; v, tl. 'bvar_case['v; 'tl]; op, bterms. 'term_case['op; 'bterms]} >> unfold_match_term
let fold_match_bterm = makeFoldC << match_bterm{'t; sl, t. 'body['sl; 't]} >> unfold_match_bterm

(************************************************************************
 * REDUCTION                                                            *
 ************************************************************************)

interactive_rw reduce_match_term_bvar :
   match_term{bvar{'v; 'tl}; x, y. 'bvar_case['x; 'y]; u, v. 'term_case['u; 'v]} <-->
      'bvar_case['v; 'tl]

interactive_rw reduce_match_term_term :
   match_term{term{'op; 'bterms}; x, y. 'bvar_case['x; 'y]; u, v. 'term_case['u; 'v]} <-->
      'term_case['op; 'bterms]

interactive_rw reduce_match_bterm :
   match_bterm{bterm{'sl; 't}; u, v. 'body['u; 'v]} <--> 'body['sl; 't]

(*
 * Bterm.
 *)
interactive_rw reduce_bterm_term :
   bterm_term{bterm{'sl; 't}} <--> 't

let resource reduce += [
   << match_term{bvar{'v; 'tl}; x, y. 'bvar_case['x; 'y]; u, v. 'term_case['u; 'v]} >>, reduce_match_term_bvar;
   << match_term{term{'op; 'bterms}; x, y. 'bvar_case['x; 'y]; u, v. 'term_case['u; 'v]} >>, reduce_match_term_term;
   << bterm_term{bterm{'sl; 't}} >>, reduce_bterm_term;
   << match_bterm{bterm{'sl; 't}; u, v. 'body['u; 'v]} >>, reduce_match_bterm
]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Operators.
 *)
prim operator_type {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{operator_type} } =
   it

prim eq_op_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'op1 IN operator_type } -->
   [wf] sequent [squash] { 'H >- 'op2 IN operator_type } -->
   sequent ['ext] { 'H >- eq_op{'op1; 'op2} IN bool } =
   it

prim eq_op_ref 'H :
   [wf] sequent [squash] { 'H >- 'op IN operator_type } -->
   sequent ['ext] { 'H >- "assert"{eq_op{'op; 'op}} } =
   it

prim eq_op_sym  'H :
   [wf] sequent [squash] { 'H >- 'op1 IN operator_type } -->
   [wf] sequent [squash] { 'H >- 'op2 IN operator_type } -->
   [wf] sequent [squash] { 'H >- "assert"{eq_op{'op2; 'op1}} } -->
   sequent [squash] { 'H >- "assert"{eq_op{'op1; 'op2}} } =
   it

prim eq_op_trans 'H 'op2 :
   sequent [squash] { 'H >- 'op1 IN operator_type } -->
   sequent [squash] { 'H >- 'op2 IN operator_type } -->
   sequent [squash] { 'H >- 'op3 IN operator_type } -->
   sequent [squash] { 'H >- "assert"{eq_op{'op1; 'op2}} } -->
   sequent [squash] { 'H >- "assert"{eq_op{'op2; 'op3}} } -->
   sequent [squash] { 'H >- "assert"{eq_op{'op1; 'op3}} } =
   it

(*
 * Bterms.
 *)
interactive raw_bterm_type {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   sequent ['ext] { 'H >- "type"{raw_bterm_type{'T}} }

(*
 * Bvars.
 *)
interactive bvar_type {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   sequent ['ext] { 'H >- "type"{bvar_type{'T}} }

(*
 * Terms.
 *)
interactive raw_term_type2 {| intro [] |} 'H :
   sequent ['ext] { 'H >- "type"{raw_term_type} }

interactive bvar_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'v IN var_type } -->
   [wf] sequent [squash] { 'H >- 'tl IN list{raw_term_type} } -->
   sequent ['ext] { 'H >- bvar{'v; 'tl} IN raw_term_type }

interactive bterm_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'vl IN list{var_type} } -->
   [wf] sequent [squash] { 'H >- 't IN 'T } -->
   sequent ['ext] { 'H >- bterm{'vl; 't} IN raw_bterm_type{'T} }

interactive term_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- 'op IN operator_type } -->
   [wf] sequent [squash] { 'H >- 'bterms IN list{raw_bterm_type{raw_term_type}} } -->
   sequent ['ext] { 'H >- term{'op; 'bterms} IN raw_term_type }

interactive term_elim1 {| elim [ThinOption thinT] |} 'H 'J 'T 'y 'z 'w 'v 'op 'bterms 'terms :
   [main] sequent ['ext] { 'H; x: raw_term_type; 'J['x];
      T: univ[1:l];
      y: subtype{'T; raw_term_type};
      z: (w: 'T -> 'C['w]);
      op: operator_type;
      bterms : list{raw_bterm_type{'T}}
      >- 'C[term{'op; 'bterms}] } -->
   [main] sequent ['ext] { 'H; x: raw_term_type; 'J['x];
      T: univ[1:l];
      y: subtype{'T; raw_term_type};
      z: (w: 'T -> 'C['w]);
      v: var_type;
      terms: list{'T}
      >- 'C[bvar{'v; 'terms}] } -->
   sequent ['ext] { 'H; x: raw_term_type; 'J['x] >- 'C['x] }

interactive bterm_term_wf {| intro [] |} 'H :
   [wf] sequent [squash] { 'H >- "type"{'T} } -->
   [wf] sequent [squash] { 'H >- 't IN raw_bterm_type{'T} } -->
   sequent ['ext] { 'H >- bterm_term{'t} IN 'T }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let eq_opRefT p =
   eq_op_ref (Sequent.hyp_count_addr p) p

let eq_opSymT p =
   eq_op_sym (Sequent.hyp_count_addr p) p

let eq_opTransT t p =
   eq_op_trans (Sequent.hyp_count_addr p) t p

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
