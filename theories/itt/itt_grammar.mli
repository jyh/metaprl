(*
 * Base grammar for ITT.
 * This defines just some meta-terms:
 *    1. second-order variables
 *    2. contexts
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends Base_theory

(************************************************************************
 * LExing basics.
 *)
declare itt          : Lexer

declare tok_eof      : Terminal

(*
 * Comments.
 *)
lex_token itt : "[[:space:]]+"    (* Ignored *)
lex_token itt : "[(][*]" "[*][)]" (* Ignored *)

(*
 * Nested quotations.
 *)
declare tok_quotation{'e : 'a} : Terminal

lex_token itt : "<:[_[:alpha:]][_[:alnum:]]*<|<<" ">>" --> tok_quotation{xquotation[arg1:s, lexeme:s]}

(*
 * End-of-file.
 *)
lex_token itt : "\'" --> tok_eof

(*
 * Base precedences.
 *)
declare prec_min : Precedence

lex_prec nonassoc [prec_min]

(************************************************************************
 * Lexing.
 *)

(* Identifiers *)
declare tok_id[v:s]            : Terminal

(* Numbers *)
declare tok_int[i:n]           : Terminal

(* Strings *)
declare tok_string[s:s]        : Terminal

(*
 * Keywords.
 * Most of the keywords are defined in subtheories.
 *)
declare tok_let                : Terminal
declare tok_in                 : Terminal
declare tok_decide             : Terminal
declare tok_match              : Terminal
declare tok_with               : Terminal
declare tok_end                : Terminal

(* Symbols *)
declare tok_dot                : Terminal
declare tok_comma              : Terminal
declare tok_semi               : Terminal
declare tok_colon              : Terminal
declare tok_bang               : Terminal
declare tok_hash               : Terminal
declare tok_at                 : Terminal
declare tok_plus               : Terminal
declare tok_minus              : Terminal
declare tok_star               : Terminal
declare tok_pipe               : Terminal
declare tok_equal              : Terminal
declare tok_arrow              : Terminal
declare tok_lt                 : Terminal
declare tok_gt                 : Terminal
declare tok_left_brack         : Terminal
declare tok_right_brack        : Terminal
declare tok_left_context       : Terminal
declare tok_right_context      : Terminal
declare tok_turnstile          : Terminal
declare tok_longrightarrow     : Terminal
declare tok_longleftrightarrow : Terminal
declare tok_left_paren         : Terminal
declare tok_right_paren        : Terminal
declare tok_left_curly         : Terminal
declare tok_right_curly        : Terminal
declare tok_colon_colon        : Terminal
declare tok_tilde              : Terminal
declare tok_backslash          : Terminal
declare tok_squote             : Terminal

(* Identifiers *)
lex_token itt : "[_[:alpha:]][_[:alnum:]]*" --> tok_id[lexeme:s]

(* Numbers *)
lex_token itt : "[[:digit:]]+" --> tok_int[lexeme:n]

(* Strings *)
lex_token itt : "\"\(\\.|[^\"]*\)\"" --> tok_string[arg1:s]

(* Keywords *)
lex_token itt : "let"        --> tok_let
lex_token itt : "decide"     --> tok_decide
lex_token itt : "match"      --> tok_match
lex_token itt : "with"       --> tok_with
lex_token itt : "in"         --> tok_in
lex_token itt : "end"        --> tok_end

(* Symbols *)
lex_token itt : "[.]"        --> tok_dot
lex_token itt : ","          --> tok_comma
lex_token itt : ";"          --> tok_semi
lex_token itt : ":"          --> tok_colon
lex_token itt : "!"          --> tok_bang
lex_token itt : "#"          --> tok_hash
lex_token itt : "@"          --> tok_at
lex_token itt : "~"          --> tok_tilde
lex_token itt : "[+]"        --> tok_plus
lex_token itt : "-"          --> tok_minus
lex_token itt : "[*]"        --> tok_star
lex_token itt : "[|]"        --> tok_pipe
lex_token itt : "="          --> tok_equal
lex_token itt : "<"          --> tok_lt
lex_token itt : ">"          --> tok_gt
lex_token itt : "[(]"        --> tok_left_paren
lex_token itt : "[)]"        --> tok_right_paren
lex_token itt : "\["         --> tok_left_brack
lex_token itt : "\]"         --> tok_right_brack
lex_token itt : "\\"         --> tok_backslash
lex_token itt : "[{]"        --> tok_left_curly
lex_token itt : "[}]"        --> tok_right_curly
lex_token itt : "'"          --> tok_squote
lex_token itt : "<[|]"       --> tok_left_context
lex_token itt : "[|]>"       --> tok_right_context
lex_token itt : "::"         --> tok_colon_colon
lex_token itt : "->"         --> tok_arrow
lex_token itt : ">-"         --> tok_turnstile
lex_token itt : "-->"        --> tok_longrightarrow
lex_token itt : "<-->"       --> tok_longleftrightarrow

(*
 * Precedences.  Pre-declare most of the precedence levels here
 * because it is often hard to decide what goes where when precedences
 * are scattered around.  You can always squeeze in a new precedence
 * level with the following sequence.
 *    lex_prec ... [prec_new] > prec_before
 *    lex_prec ... prec_new < prec_after
 *)
declare prec_mimplies  : Precedence
declare prec_turnstile : Precedence
declare prec_let       : Precedence
declare prec_comma     : Precedence
declare prec_colon     : Precedence
declare prec_arrow     : Precedence
declare prec_implies   : Precedence
declare prec_or        : Precedence
declare prec_and       : Precedence
declare prec_in        : Precedence
declare prec_equal     : Precedence
declare prec_add       : Precedence
declare prec_mul       : Precedence
declare prec_band      : Precedence
declare prec_union     : Precedence
declare prec_prod      : Precedence
declare prec_iff       : Precedence
declare prec_apply     : Precedence
declare prec_not       : Precedence
declare prec_rel       : Precedence
declare prec_cons      : Precedence

lex_prec right    [prec_mimplies] > prec_min
lex_prec right    [prec_turnstile] > prec_mimplies
lex_prec right    [prec_let] > prec_turnstile
lex_prec right    [prec_comma] > prec_let
lex_prec right    [prec_colon] > prec_comma
lex_prec right    [prec_iff] > prec_colon
lex_prec right    [prec_implies] > prec_iff
lex_prec right    [prec_or] > prec_implies
lex_prec right    [prec_and] > prec_or
lex_prec right    [prec_in] > prec_and
lex_prec right    [prec_equal] > prec_in
lex_prec left     [prec_union] > prec_equal
lex_prec right    [prec_arrow] > prec_union
lex_prec right    [prec_prod] > prec_arrow
lex_prec right    [prec_cons] > prec_prod
lex_prec nonassoc [prec_rel] > prec_cons
lex_prec left     [prec_add] > prec_rel
lex_prec left     [prec_mul] > prec_add
lex_prec left     [prec_band] > prec_mul
lex_prec left     [prec_apply] > prec_band
lex_prec right    [prec_not] > prec_apply

lex_prec right    [tok_longrightarrow; tok_longleftrightarrow] = prec_mimplies
lex_prec right    [tok_turnstile] = prec_turnstile
lex_prec right    [tok_plus; tok_minus] = prec_union
lex_prec right    [tok_star] = prec_prod
lex_prec right    [tok_arrow] = prec_arrow
lex_prec right    [tok_colon] = prec_colon
lex_prec right    [tok_comma] = prec_comma
lex_prec right    [tok_let; tok_decide; tok_match; tok_with; tok_in] = prec_let
lex_prec left     [tok_at] = prec_apply
lex_prec right    [tok_colon_colon] = prec_cons
lex_prec nonassoc [tok_tilde; tok_dot; tok_hash; tok_squote] = prec_not
lex_prec right    [tok_pipe] = prec_let

(************************************************
 * Utilities.
 *)
declare opt_pipe       : Nonterminal
declare comma_or_semi  : Nonterminal

production opt_pipe <-- (* empty *)

production opt_pipe <--
   tok_pipe

production comma_or_semi <--
   tok_comma

production comma_or_semi <--
   tok_semi

(************************************************
 * Second-order variables and contexts.
 *
 *     v                   : a simple variable
 *     !v                  : a free first-order variable
 *     v[e1; ...; en]      : a second-order variable with arguments e1..en
 *     v<|H|>[e1; ...; en] : a second-order variable with a context argument
 *     <H>                 : a simple context (normally displayed as Gamma)
 *     <H<|J|> >           : a context with a context argument
 *     <#H>                : a non-binding context
 *)

declare itt_term{'e : Term} : Nonterminal

(* Second-order variables *)
declare iform parsed_var[v:s] : 'a
declare iform parsed_fovar[v:s] : 'a
declare iform parsed_sovar[v:s]{'contexts : Dform; 'args : Dform} : 'a

declare itt_sovar{'e : 'a} : Nonterminal
declare itt_contexts{'l : Dform} : Nonterminal
declare itt_inner_contexts{'l : Dform} : Nonterminal
declare itt_nonempty_contexts{next : Dform. 'l : Dform} : Nonterminal
declare itt_so_args{'l : Dform} : Nonterminal
declare itt_opt_so_args{'l : Dform} : Nonterminal
declare itt_so_inner_args{'l : Dform} : Nonterminal
declare itt_so_nonempty_args{next : Dform. 'l : Dform} : Nonterminal

(* Second-order vars *)
production itt_sovar{'v} <--
   tok_id[v:s]

production itt_sovar{parsed_fovar[v:s]} <--
   tok_bang; tok_id[v:s]

production itt_sovar{parsed_sovar[v:s]{xcons{'v; xnil}; 'args}} <--
   tok_id[v:s]; itt_so_args{'args}

production itt_sovar{parsed_sovar[v:s]{'contexts; 'args}} <--
   tok_id[v:s]; itt_contexts{'contexts}; itt_opt_so_args{'args}

production itt_contexts{'contexts} <--
   tok_left_context; itt_inner_contexts{'contexts}; tok_right_context

production itt_inner_contexts{xnil} <-- (* empty *)

production itt_inner_contexts{'contexts[xnil]} <--
   itt_nonempty_contexts{next. 'contexts['next]}

production itt_nonempty_contexts{next. xcons{'v; 'next}} <--
   tok_id[v:s]

production itt_nonempty_contexts{next. 'contexts[xcons{'v; 'next}]} <--
   itt_nonempty_contexts{next. 'contexts['next]}; tok_comma; tok_id[v:s]

production itt_opt_so_args{xnil} <-- (* empty *)

production itt_opt_so_args{'args} <--
   itt_so_args{'args}

production itt_so_args{'args} <--
   tok_left_brack; itt_so_inner_args{'args}; tok_right_brack

production itt_so_inner_args{xnil} <-- (* empty *)

production itt_so_inner_args{'args[xnil]} <--
   itt_so_nonempty_args{next. 'args['next]}

production itt_so_nonempty_args{next. xcons{'arg; 'next}} <--
   itt_term{'arg}

production itt_so_nonempty_args{next. 'args[xcons{'arg; 'next}]} <--
   itt_so_nonempty_args{next. 'args['next]}; tok_semi; itt_term{'arg}

(* Contexts *)
declare itt_context{'e : 'a} : Nonterminal

production itt_context{xhypcontext[v:v]{xcons{'v; xnil}; 'args}} <--
   tok_lt; tok_id[v:s]; itt_opt_so_args{'args}; tok_gt

production itt_context{xhypcontext[v:v]{'contexts; 'args}} <--
   tok_lt; tok_id[v:s]; itt_contexts{'contexts}; itt_opt_so_args{'args}; tok_gt

production itt_context{xhypcontext[v:v]{xcons{parsed_var["#"]; xcons{'v; xnil}}; 'args}} <--
   tok_lt; tok_hash; tok_id[v:s]; itt_opt_so_args{'args}; tok_gt

production itt_context{xhypcontext[v:v]{xcons{parsed_var["#"]; 'contexts}; 'args}} <--
   tok_lt; tok_hash; tok_id[v:s]; itt_contexts{'contexts}; itt_opt_so_args{'args}; tok_gt

(************************************************
 * Terms.
 *)

(*
 * Terms are composed of applications.
 *)
declare itt_apply_term{'e : Term} : Nonterminal
declare itt_simple_term{'e : Term} : Nonterminal

production itt_term{'e} <--
    itt_apply_term{'e}

production itt_apply_term{'e} <--
    itt_simple_term{'e}

production itt_simple_term{'e} <--
    itt_sovar{'e}

production itt_simple_term{'e} <--
    tok_quotation{'e}

production itt_simple_term{'e} <--
    tok_left_paren; itt_term{'e}; tok_right_paren

(************************************************
 * Generic terms using the normal syntax.
 *)

(*
 * An operator is a pathname of quoted identifiers.
 *)
declare itt_opname{'op : Dform} : Nonterminal

production itt_opname{xlist_sequent{| xopname[x:s] |}} <--
   tok_string[x:s]

production itt_opname{xlist_sequent{| <H>; xopname[x:s] |}} <--
   itt_opname{xlist_sequent{| <H> |}}; tok_dot; tok_string[x:s]

(*
 * Parameter kinds are a list of string-or-word.
 *    kind ::= sw
 *          | kind ! sw
 *)
declare itt_param_kind_exp{'p : Dform} : Nonterminal
declare itt_param_kind{'p : Dform} : Nonterminal

production itt_param_kind_exp{xparam_id[x:s]} <--
   tok_id[x:s]

production itt_param_kind_exp{xparam_string[x:s]} <--
   tok_string[x:s]

production itt_param_kind{xlist_sequent{| 'p |}} <--
   itt_param_kind_exp{'p}

production itt_param_kind{xlist_sequent{| <H>; 'p |}} <--
   itt_param_kind{xlist_sequent{| <H> |}}; tok_bang; itt_param_kind_exp{'p}

(*
 * A param is:
 *    kind : string_or_id+
 *
 *    p_exp ::= <int>
 *           |  - <int>
 *           |  <string>
 *           |  <id>
 *           |  p_exp'
 *           |  p_exp | p_exp
 *           |  ( term )
 *
 *    p ::= p_exp
 *       |  p_exp : kind
 *)
declare itt_param_exp{'p : Dform} : Nonterminal
declare itt_param{'p : Dform} : Nonterminal
declare itt_param_list{'p : Dform} : Nonterminal
declare itt_param_nonempty_list{'l : Dform} : Nonterminal
declare itt_params{'l : Dform} : Nonterminal

production itt_param_exp{xparam_int[i:n]} <--
   tok_int[i:n]

production itt_param_exp{xparam_neg[i:n]} <--
   tok_minus; tok_int[i:n]

production itt_param_exp{xparam_string[s:s]} <--
   tok_string[s:s]

production itt_param_exp{xparam_id[x:s]} <--
   tok_id[x:s]

production itt_param_exp{xparam_succ{'p}} <--
   itt_param_exp{'p}; tok_squote

production itt_param_exp{xparam_max{'p1; 'p2}} <--
   itt_param_exp{'p1}; tok_pipe; itt_param_exp{'p2}

production itt_param{xparam{'p}} <--
   itt_param_exp{'p}

production itt_param{xparam{'p; 'k}} <--
   itt_param_exp{'p}; tok_colon; itt_param_kind{'k}

production itt_param_exp{xparam_term{'t; 'k}} <--
   tok_left_paren; itt_term{'t}; tok_right_paren; itt_param_kind{'k}

(*
 * A param list is [param, ..., param]
 *)
production itt_params{xlist_sequent{||}} <--
   (* empty *)

production itt_params{'l} <--
   tok_left_brack; itt_param_list{'l}; tok_right_brack

production itt_param_list{xlist_sequent{||}} <--
   (* empty *)

production itt_param_list{'l} <--
   itt_param_nonempty_list{'l}

production itt_param_nonempty_list{xlist_sequent{| 'p |}} <--
   itt_param{'p}

production itt_param_nonempty_list{xlist_sequent{| <H>; 'p |}} <--
   itt_param_nonempty_list{xlist_sequent{| <H> |}}; comma_or_semi; itt_param{'p}

(*
 * Bterms.
 *)
declare itt_bterm{'t : Dform} : Nonterminal
declare itt_bterm_bind{'t : Dform} : Nonterminal
declare itt_bterms{'t : Dform} : Nonterminal
declare itt_bterms_list{'t : Dform} : Nonterminal
declare itt_bterms_nonempty_list{'t : Dform} : Nonterminal

(*
 * A bterm is a single term, or \v1, ..., vn. term
 *)
production itt_bterm{'t} <--
   itt_term{'t}

production itt_bterm{'t} <--
   itt_bterm_bind{'t}

production itt_bterm_bind{xbterm{| x: it |}} <--
   tok_backslash; tok_id[x:s]

production itt_bterm_bind{xbterm{| <H>; x: it |}} <--
   itt_bterm_bind{xbterm{| <H> |}}; tok_comma; tok_id[x:s]

production itt_bterm_bind{xbterm{| <H> >- 't |}} <--
   itt_bterm_bind{xbterm{| <H> |}}; tok_dot; itt_term{'t}

(*
 * Bterms are {...}
 *)
production itt_bterms{xlist_sequent{||}} <--
   (* empty *)

production itt_bterms{'t} <--
   tok_left_curly; itt_bterms_list{'t}; tok_right_curly

production itt_bterms_list{xlist_sequent{||}} <--
   (* empty *)

production itt_bterms_list{'l} <--
   itt_bterms_nonempty_list{'l}

production itt_bterms_nonempty_list{xlist_sequent{| 't |}} <--
   itt_bterm{'t}

production itt_bterms_nonempty_list{xlist_sequent{| <H>; 't |}} <--
   itt_bterms_nonempty_list{xlist_sequent{| <H> |}}; tok_semi; itt_bterm{'t}

(*
 * The operator must be quoted.
 *)
production itt_simple_term{xterm{'op; 'p; 't}} <--
   itt_opname{'op}; itt_params{'p}; itt_bterms{'t}

(************************************************************************
 * Meta-terms.
 *)
declare typeclass parsed_hyps_exp

declare sequent [parsed_hyps] { Term : Term >- Ignore } : parsed_hyps_exp

declare itt_meta_term{'p : MTerm} : Nonterminal
declare itt_hyps{'e : parsed_hyps_exp} : Nonterminal

production itt_meta_term{meta_theorem{sequent { <H> >- 'e }}} <--
   itt_hyps{parsed_hyps{| <H> |}}; tok_turnstile; itt_term{'e}

production itt_meta_term{meta_implies{'e1; 'e2}} <--
   itt_meta_term{'e1}; tok_longrightarrow; itt_meta_term{'e2}

(*
 * Hypothesis.
 *)
declare itt_nonempty_hyps{'e : parsed_hyps_exp} : Nonterminal
declare itt_hyp[x:s]{'e : 'a} : Nonterminal

production itt_hyps{parsed_hyps{||}} <-- (* empty *)

production itt_hyps{'e} <--
   itt_nonempty_hyps{'e}

production itt_nonempty_hyps{parsed_hyps{| x: 'e |}} <--
   itt_hyp[x:s]{'e}

production itt_nonempty_hyps{parsed_hyps{| <hyps>; x : 'e |}} <--
   itt_nonempty_hyps{parsed_hyps{| <hyps> |}}; tok_semi; itt_hyp[x:s]{'e}

production itt_hyp[x:s]{'e} <--
   tok_id[x:s]; tok_colon; itt_term{'e}

production itt_hyp["_"]{'e} <--
   itt_term{'e}

production itt_hyp[""]{'c} <--
   itt_context{'c}

(*
 * Meta-rewrite allows any term, not just sequents.
 *)
declare itt_meta_rewrite{'e : MTerm} : Nonterminal

production itt_meta_rewrite{meta_theorem{'e}} <--
   itt_term{'e}

production itt_meta_rewrite{meta_iff{'e1; 'e2}} <--
   itt_meta_rewrite{'e1}; tok_longleftrightarrow; itt_meta_rewrite{'e2}

(*
 * Add a toplevel production.
 *)
declare itt{'e : Term} : Nonterminal
declare itt_mterm{'e : MTerm} : Nonterminal
declare itt_rule{'e : MTerm} : Nonterminal
declare itt_rw{'e : MTerm} : Nonterminal

parser itt{'e} : itt
parser itt_mterm{'e} : itt
parser itt_rule{'e} : itt
parser itt_rw{'e} : itt

production itt{'e} <--
   itt_term{'e}; tok_eof

production itt_mterm{'e} <--
   itt_meta_term{'e}; tok_eof

production itt_rule{'e} <--
   itt_meta_term{'e}; tok_eof

production itt_rw{'e} <--
   itt_meta_rewrite{'e}; tok_eof

(************************************************************************
 * Iforms.
 *)
iform unfold_itt :
   itt{'e}
   <-->
   'e

iform unfold_itt_mterm :
   itt_mterm{'e}
   <-->
   'e

iform unfold_itt_rule :
   itt_rule{'e}
   <-->
   'e

iform unfold_itt_rw :
   itt_rw{'e}
   <-->
   'e

(*
 * First-order variables.
 *)
iform var :
   parsed_var[v:s]
   <-->
   'v

iform fovar_std :
   parsed_fovar[v1:s]
   <-->
   xsovar[v1:v]{xcons{parsed_var["!"]; xnil}; xnil}

(*
 * Second-order variables.
 *)
iform var_id :
   parsed_sovar[x:s]{'contexts; 'args}
   <-->
   xsovar[x:v]{'contexts; 'args}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
