(*
 * Define terms.
 *)

include Itt_theory

include Refl_var

open Refiner.Refiner.RefineError
open Mp_resource

open Tacticals
open Conversionals
open Var

open Itt_equal

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

let reduce_info =
   [<< match_term{bvar{'v; 'tl}; x, y. 'bvar_case['x; 'y]; u, v. 'term_case['u; 'v]} >>, reduce_match_term_bvar;
    << match_term{term{'op; 'bterms}; x, y. 'bvar_case['x; 'y]; u, v. 'term_case['u; 'v]} >>, reduce_match_term_term;
    << bterm_term{bterm{'sl; 't}} >>, reduce_bterm_term;
    << match_bterm{bterm{'sl; 't}; u, v. 'body['u; 'v]} >>, reduce_match_bterm]

let reduce_resource = add_reduce_info reduce_resource reduce_info

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Operators.
 *)
prim operator_type 'H : :
   sequent ['ext] { 'H >- "type"{operator_type} } =
   it

prim eq_op_wf 'H :
   sequent [squash] { 'H >- member{operator_type; 'op1} } -->
   sequent [squash] { 'H >- member{operator_type; 'op2} } -->
   sequent ['ext] { 'H >- member{bool; eq_op{'op1; 'op2}} } =
   it

prim eq_op_ref 'H :
   sequent [squash] { 'H >- member{operator_type; 'op} } -->
   sequent ['ext] { 'H >- "assert"{eq_op{'op; 'op}} } =
   it

prim eq_op_sym 'H :
   sequent [squash] { 'H >- member{operator_type; 'op1} } -->
   sequent [squash] { 'H >- member{operator_type; 'op2} } -->
   sequent [squash] { 'H >- "assert"{eq_op{'op2; 'op1}} } -->
   sequent [squash] { 'H >- "assert"{eq_op{'op1; 'op2}} } =
   it

prim eq_op_trans 'H 'op2 :
   sequent [squash] { 'H >- member{operator_type; 'op1} } -->
   sequent [squash] { 'H >- member{operator_type; 'op2} } -->
   sequent [squash] { 'H >- member{operator_type; 'op3} } -->
   sequent [squash] { 'H >- "assert"{eq_op{'op1; 'op2}} } -->
   sequent [squash] { 'H >- "assert"{eq_op{'op2; 'op3}} } -->
   sequent [squash] { 'H >- "assert"{eq_op{'op1; 'op3}} } =
   it

(*
 * Bterms.
 *)
interactive raw_bterm_type 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent ['ext] { 'H >- "type"{raw_bterm_type{'T}} }

(*
 * Bvars.
 *)
interactive bvar_type 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent ['ext] { 'H >- "type"{bvar_type{'T}} }

(*
 * Terms.
 *)
interactive raw_term_type2 'H : :
   sequent ['ext] { 'H >- "type"{raw_term_type} }

interactive bvar_wf 'H :
   sequent [squash] { 'H >- member{var_type; 'v} } -->
   sequent [squash] { 'H >- member{list{raw_term_type}; 'tl} } -->
   sequent ['ext] { 'H >- member{raw_term_type; bvar{'v; 'tl}} }

interactive bterm_wf 'H :
   sequent [squash] { 'H >- member{list{var_type}; 'vl} } -->
   sequent [squash] { 'H >- member{'T; 't} } -->
   sequent ['ext] { 'H >- member{raw_bterm_type{'T}; bterm{'vl; 't}} }

interactive term_wf 'H :
   sequent [squash] { 'H >- member{operator_type; 'op} } -->
   sequent [squash] { 'H >- member{list{raw_bterm_type{raw_term_type}}; 'bterms} } -->
   sequent ['ext] { 'H >- member{raw_term_type; term{'op; 'bterms}} }

interactive term_elim1 'H 'J 'T 'y 'z 'w 'v 'op 'bterms 'terms :
   sequent ['ext] { 'H; x: raw_term_type; 'J['x];
      T: univ[1:l];
      y: subtype{'T; raw_term_type};
      z: (w: 'T -> 'C['w]);
      op: operator_type;
      bterms : list{raw_bterm_type{'T}}
      >- 'C[term{'op; 'bterms}] } -->
   sequent ['ext] { 'H; x: raw_term_type; 'J['x];
      T: univ[1:l];
      y: subtype{'T; raw_term_type};
      z: (w: 'T -> 'C['w]);
      v: var_type;
      terms: list{'T}
      >- 'C[bvar{'v; 'terms}] } -->
   sequent ['ext] { 'H; x: raw_term_type; 'J['x] >- 'C['x] }

interactive bterm_term_wf 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent [squash] { 'H >- member{raw_bterm_type{'T}; 't} } -->
   sequent ['ext] { 'H >- member{'T; bterm_term{'t}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let wrap_type tac i p =
   if i = 0 then
      tac p
   else
      raise (RefineError ("wrap_type", StringError "no elimination form"))

let d_operator_typeT p =
   operator_type (Sequent.hyp_count_addr p) p

let operator_type_term = << "type"{operator_type} >>

let d_resource = Mp_resource.improve d_resource (operator_type_term, wrap_type d_operator_typeT)

let d_raw_bterm_type_typeT p =
   raw_bterm_type (Sequent.hyp_count_addr p) p

let raw_bterm_type_type_term = << "type"{raw_bterm_type{'T}} >>

let d_resource = Mp_resource.improve d_resource (raw_bterm_type_type_term, wrap_type d_raw_bterm_type_typeT)

let d_bvar_type_typeT p =
   bvar_type (Sequent.hyp_count_addr p) p

let bvar_type_type_term = << "type"{bvar_type{'T}} >>

let d_resource = Mp_resource.improve d_resource (bvar_type_type_term, wrap_type d_bvar_type_typeT)

let d_raw_term_type_typeT p =
   raw_term_type2 (Sequent.hyp_count_addr p) p

let raw_term_type_type_term = << "type"{raw_term_type} >>

let d_resource = Mp_resource.improve d_resource (raw_term_type_type_term, wrap_type d_raw_term_type_typeT)

let d_bvar_wfT p =
   (bvar_wf (Sequent.hyp_count_addr p)
    thenT addHiddenLabelT "wf") p

let bvar_member_term = << member{raw_term_type; bvar{'v; 'tl}} >>

let d_resource = Mp_resource.improve d_resource (bvar_member_term, wrap_intro d_bvar_wfT)

let d_bterm_wfT p =
   (bterm_wf (Sequent.hyp_count_addr p)
    thenT addHiddenLabelT "wf") p

let bterm_member_term = << member{raw_term_type; bterm{'sl; 't}} >>

let d_resource = Mp_resource.improve d_resource (bterm_member_term, wrap_intro d_bterm_wfT)

let d_term_wfT p =
   (term_wf (Sequent.hyp_count_addr p)
    thenT addHiddenLabelT "wf") p

let term_member_term = << member{raw_term_type; term{'op; 'tl}} >>

let d_resource = Mp_resource.improve d_resource (term_member_term, wrap_intro d_term_wfT)

let d_raw_term_typeT i p =
   if i = 0 then
      raise (RefineError ("d_termT", StringError "no introduction form"))
   else
      let j, k = Sequent.hyp_indices p i in
      let t, y, z, w, v, op, bterms, terms = maybe_new_vars8 p "T" "y" "z" "u" "v" "op" "bterms" "terms" in
         term_elim1 j k t y z w v op bterms terms p

let raw_term_type_term = << raw_term_type >>

let d_resource = Mp_resource.improve d_resource (raw_term_type_term, d_raw_term_typeT)

(*
 * Bterm operations.
 *)
let d_bterm_term_wfT p =
   (bterm_term_wf (Sequent.hyp_count_addr p)
    thenT addHiddenLabelT "wf") p

let bterm_term_type_term = << member{'T; bterm_term{'t}} >>

let d_resource = Mp_resource.improve d_resource (bterm_term_type_term, wrap_intro d_bterm_term_wfT)

(*
 * Operator equality.
 *)
let d_eq_op_wfT p =
   (eq_op_wf (Sequent.hyp_count_addr p)
    thenT addHiddenLabelT "wf") p

let eq_op_wf_term = << member{bool; eq_op{'op1; 'op2}} >>

let d_resource = Mp_resource.improve d_resource (eq_op_wf_term, wrap_intro d_eq_op_wfT)

let eq_opRefT p =
   (eq_op_ref (Sequent.hyp_count_addr p)
    thenT addHiddenLabelT "wf") p

let eq_opSymT p =
   (eq_op_sym (Sequent.hyp_count_addr p)
    thenLT [addHiddenLabelT "wf";
            addHiddenLabelT "wf";
            addHiddenLabelT "main"]) p

let eq_opTransT t p =
   (eq_op_trans (Sequent.hyp_count_addr p) t
    thenLT [addHiddenLabelT "wf";
            addHiddenLabelT "wf";
            addHiddenLabelT "wf";
            addHiddenLabelT "main";
            addHiddenLabelT "main"]) p

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
