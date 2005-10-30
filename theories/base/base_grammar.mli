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
extends Perv
extends Base_trivial
extends Base_rewrite

(************************************************************************
 * Lexing basics.
 *)
declare xterm        : Lexer

declare tok_eof      : Terminal

(*
 * Comments.
 *)
lex_token xterm : "[[:space:]]+"    (* Ignored *)
lex_token xterm : "[(][*]" "[*][)]" (* Ignored *)

(*
 * Nested quotations.
 *)
declare tok_quotation{'e : 'a} : Terminal

lex_token xterm : "<:[_[:alpha:]][_[:alnum:]]*<|<<" ">>" --> tok_quotation{xquotation[arg1:s, lexeme:s]}

(*
 * End-of-file.
 *)
lex_token xterm : "\'" --> tok_eof

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
declare tok_type               : Terminal
declare tok_sequent            : Terminal

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
declare tok_left_brace         : Terminal
declare tok_right_brace        : Terminal
declare tok_colon_colon        : Terminal
declare tok_tilde              : Terminal
declare tok_backslash          : Terminal
declare tok_squote             : Terminal
declare tok_bquote             : Terminal
declare tok_dollar             : Terminal

(* Identifiers *)
lex_token xterm : "[_[:alpha:]][_[:alnum:]]*" --> tok_id[lexeme:s]

(* Numbers *)
lex_token xterm : "[[:digit:]]+" --> tok_int[lexeme:n]

(* Strings *)
lex_token xterm : "\"\(\\.|[^\"]*\)\"" --> tok_string[arg1:s]

(* Keywords *)
lex_token xterm : "let"        --> tok_let
lex_token xterm : "decide"     --> tok_decide
lex_token xterm : "match"      --> tok_match
lex_token xterm : "with"       --> tok_with
lex_token xterm : "in"         --> tok_in
lex_token xterm : "end"        --> tok_end
lex_token xterm : "type"       --> tok_type
lex_token xterm : "sequent"    --> tok_sequent

(* Symbols *)
lex_token xterm : "[.]"        --> tok_dot
lex_token xterm : ","          --> tok_comma
lex_token xterm : ";"          --> tok_semi
lex_token xterm : ":"          --> tok_colon
lex_token xterm : "!"          --> tok_bang
lex_token xterm : "#"          --> tok_hash
lex_token xterm : "@"          --> tok_at
lex_token xterm : "~"          --> tok_tilde
lex_token xterm : "[+]"        --> tok_plus
lex_token xterm : "-"          --> tok_minus
lex_token xterm : "[*]"        --> tok_star
lex_token xterm : "[|]"        --> tok_pipe
lex_token xterm : "[$]"        --> tok_dollar
lex_token xterm : "="          --> tok_equal
lex_token xterm : "<"          --> tok_lt
lex_token xterm : ">"          --> tok_gt
lex_token xterm : "[(]"        --> tok_left_paren
lex_token xterm : "[)]"        --> tok_right_paren
lex_token xterm : "\["         --> tok_left_brack
lex_token xterm : "\]"         --> tok_right_brack
lex_token xterm : "\\"         --> tok_backslash
lex_token xterm : "[{]"        --> tok_left_brace
lex_token xterm : "[}]"        --> tok_right_brace
lex_token xterm : "'"          --> tok_squote
lex_token xterm : "<[|]"       --> tok_left_context
lex_token xterm : "[|]>"       --> tok_right_context
lex_token xterm : "::"         --> tok_colon_colon
lex_token xterm : "->"         --> tok_arrow
lex_token xterm : ">-"         --> tok_turnstile
lex_token xterm : "-->"        --> tok_longrightarrow
lex_token xterm : "<-->"       --> tok_longleftrightarrow

(*
 * Precedences.  Pre-declare most of the precedence levels here
 * because it is often hard to decide what goes where when precedences
 * are scattered around.  You can always squeeze in a new precedence
 * level with the following sequence.
 *    lex_prec ... [prec_new] > prec_before
 *    lex_prec ... prec_new < prec_after
 *)
declare prec_mimplies  : Precedence
declare prec_miff      : Precedence
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
lex_prec right    [prec_miff] > prec_mimplies
lex_prec right    [prec_turnstile] > prec_miff
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

lex_prec right    [tok_longrightarrow] = prec_mimplies
lex_prec right    [tok_longleftrightarrow] = prec_miff
lex_prec right    [tok_turnstile] = prec_turnstile
lex_prec right    [tok_plus; tok_minus] = prec_union
lex_prec right    [tok_star] = prec_prod
lex_prec right    [tok_arrow] = prec_arrow
lex_prec right    [tok_colon] = prec_colon
lex_prec right    [tok_comma] = prec_comma
lex_prec right    [tok_let; tok_decide; tok_match; tok_with; tok_in] = prec_let
lex_prec left     [tok_at] = prec_apply
lex_prec right    [tok_colon_colon] = prec_cons
lex_prec nonassoc [tok_tilde; tok_dot; tok_hash; tok_squote; tok_dollar] = prec_not
lex_prec right    [tok_pipe] = prec_let

(************************************************
 * Utilities.
 *)
declare opt_pipe                : Nonterminal
declare xterm_comma_or_semi     : Nonterminal
declare xterm_id_or_string[x:s] : Nonterminal

production opt_pipe <-- (* empty *)

production opt_pipe <--
   tok_pipe

production xterm_comma_or_semi <--
   tok_comma

production xterm_comma_or_semi <--
   tok_semi

production xterm_id_or_string[x:s] <--
   tok_id[x:s]

production xterm_id_or_string[x:s] <--
   tok_string[x:s]

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

declare xterm_term{'e : Term} : Nonterminal

(* Second-order variables *)
declare iform parsed_var[v:s] : 'a
declare iform parsed_fovar[v:s] : 'a
declare iform parsed_sovar[v:s]{'contexts : Dform; 'args : Dform} : 'a

declare xterm_sovar{'e : 'a} : Nonterminal
declare xterm_contexts{'l : Dform} : Nonterminal
declare xterm_inner_contexts{'l : Dform} : Nonterminal
declare xterm_nonempty_contexts{next : Dform. 'l : Dform} : Nonterminal
declare xterm_so_args{'l : Dform} : Nonterminal
declare xterm_opt_so_args{'l : Dform} : Nonterminal
declare xterm_so_inner_args{'l : Dform} : Nonterminal
declare xterm_so_nonempty_args{next : Dform. 'l : Dform} : Nonterminal

(* Second-order vars *)
production xterm_sovar{'v} <--
   tok_id[v:s]

production xterm_sovar{parsed_sovar[v:s]{xcons{'v; xnil}; 'args}} <--
   tok_id[v:s]; xterm_so_args{'args}

production xterm_sovar{parsed_sovar[v:s]{'contexts; 'args}} <--
   tok_id[v:s]; xterm_contexts{'contexts}; xterm_opt_so_args{'args}

production xterm_contexts{'contexts} <--
   tok_left_context; xterm_inner_contexts{'contexts}; tok_right_context

production xterm_inner_contexts{xnil} <-- (* empty *)

production xterm_inner_contexts{'contexts[xnil]} <--
   xterm_nonempty_contexts{next. 'contexts['next]}

production xterm_nonempty_contexts{next. xcons{'v; 'next}} <--
   tok_id[v:s]

production xterm_nonempty_contexts{next. 'contexts[xcons{'v; 'next}]} <--
   xterm_nonempty_contexts{next. 'contexts['next]}; tok_comma; tok_id[v:s]

production xterm_opt_so_args{xnil} <-- (* empty *)

production xterm_opt_so_args{'args} <--
   xterm_so_args{'args}

production xterm_so_args{'args} <--
   tok_left_brack; xterm_so_inner_args{'args}; tok_right_brack

production xterm_so_inner_args{xnil} <-- (* empty *)

production xterm_so_inner_args{'args[xnil]} <--
   xterm_so_nonempty_args{next. 'args['next]}

production xterm_so_nonempty_args{next. xcons{'arg; 'next}} <--
   xterm_term{'arg}

production xterm_so_nonempty_args{next. 'args[xcons{'arg; 'next}]} <--
   xterm_so_nonempty_args{next. 'args['next]}; tok_semi; xterm_term{'arg}

(* Contexts *)
declare xterm_context{'e : 'a} : Nonterminal

production xterm_context{xhypcontext[v:v]{xcons{'v; xnil}; 'args}} <--
   tok_lt; tok_id[v:s]; xterm_opt_so_args{'args}; tok_gt

production xterm_context{xhypcontext[v:v]{'contexts; 'args}} <--
   tok_lt; tok_id[v:s]; xterm_contexts{'contexts}; xterm_opt_so_args{'args}; tok_gt

production xterm_context{xhypcontext[v:v]{xcons{parsed_var["#"]; xcons{'v; xnil}}; 'args}} <--
   tok_lt; tok_hash; tok_id[v:s]; xterm_opt_so_args{'args}; tok_gt

production xterm_context{xhypcontext[v:v]{xcons{parsed_var["#"]; 'contexts}; 'args}} <--
   tok_lt; tok_hash; tok_id[v:s]; xterm_contexts{'contexts}; xterm_opt_so_args{'args}; tok_gt

(************************************************
 * Terms.
 *)

(*
 * Terms are composed of applications.
 *)
declare xterm_apply_term{'e : Term} : Nonterminal
declare xterm_simple_term{'e : Term} : Nonterminal

production xterm_term{parsed_fovar[v:s]} <--
   tok_bang; tok_id[v:s]

production xterm_term{'e} <--
   xterm_apply_term{'e}

production xterm_apply_term{'e} <--
   xterm_simple_term{'e}

production xterm_simple_term{'e} <--
   xterm_sovar{'e}

production xterm_simple_term{'e} <--
   tok_quotation{'e}

production xterm_simple_term{'e} <--
   tok_left_paren; xterm_term{'e}; tok_right_paren

(************************************************
 * Generic terms using the normal syntax.
 *)

(*
 * An operator is a pathname of quoted identifiers.
 *)
declare xterm_opname{'op : Dform} : Nonterminal

production xterm_opname{xlist_sequent{| xopname[x:s] |}} <--
   tok_string[x:s]

production xterm_opname{xlist_sequent{| xopname[x:s]; xopname[y:s] |}} <--
   tok_id[x:s]; tok_bang; xterm_id_or_string[y:s]

production xterm_opname{xlist_sequent{| <H>; xopname[x:s] |}} <--
   xterm_opname{xlist_sequent{| <H> |}}; tok_bang; xterm_id_or_string[x:s]

(*
 * Parameter kinds are a list of string-or-word.
 *    kind ::= sw
 *          | kind ! sw
 *)
declare xterm_param_kind_exp{'p : Dform} : Nonterminal
declare xterm_param_kind{'p : Dform} : Nonterminal

production xterm_param_kind_exp{xparam_id[x:s]} <--
   tok_id[x:s]

production xterm_param_kind_exp{xparam_string[x:s]} <--
   tok_string[x:s]

production xterm_param_kind{xlist_sequent{| 'p |}} <--
   xterm_param_kind_exp{'p}

production xterm_param_kind{xlist_sequent{| <H>; 'p |}} <--
   xterm_param_kind{xlist_sequent{| <H> |}}; tok_bang; xterm_param_kind_exp{'p}

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
declare xterm_param_exp{'p : Dform} : Nonterminal
declare xterm_param{'p : Dform} : Nonterminal
declare xterm_param_list{'p : Dform} : Nonterminal
declare xterm_param_nonempty_list{'l : Dform} : Nonterminal
declare xterm_params{'l : Dform} : Nonterminal

production xterm_param_exp{xparam_int[i:n]} <--
   tok_int[i:n]

production xterm_param_exp{xparam_neg[i:n]} <--
   tok_minus; tok_int[i:n]

production xterm_param_exp{xparam_string[s:s]} <--
   tok_string[s:s]

production xterm_param_exp{xparam_id[x:s]} <--
   tok_id[x:s]

production xterm_param_exp{xparam_succ{'p}} <--
   xterm_param_exp{'p}; tok_squote

production xterm_param_exp{xparam_max{'p1; 'p2}} <--
   xterm_param_exp{'p1}; tok_pipe; xterm_param_exp{'p2}

production xterm_param{xparam{'p}} <--
   xterm_param_exp{'p}

production xterm_param{xparam{'p; 'k}} <--
   xterm_param_exp{'p}; tok_colon; xterm_param_kind{'k}

production xterm_param{xparam_term{'t; 'k}} <--
   tok_left_paren; xterm_term{'t}; tok_right_paren; tok_colon; xterm_param_kind{'k}

(*
 * A param list is [param, ..., param]
 *)
production xterm_params{xlist_sequent{||}} <--
   (* empty *)

production xterm_params{'l} <--
   tok_left_brack; xterm_param_list{'l}; tok_right_brack

production xterm_param_list{xlist_sequent{||}} <--
   (* empty *)

production xterm_param_list{'l} <--
   xterm_param_nonempty_list{'l}

production xterm_param_nonempty_list{xlist_sequent{| 'p |}} <--
   xterm_param{'p}

production xterm_param_nonempty_list{xlist_sequent{| <H>; 'p |}} <--
   xterm_param_nonempty_list{xlist_sequent{| <H> |}}; xterm_comma_or_semi; xterm_param{'p}

(*
 * Bterms.
 *)
declare xterm_bterm{'t : Dform} : Nonterminal
declare xterm_bterm_bind{'t : Dform} : Nonterminal
declare xterm_bterms{'t : Dform} : Nonterminal
declare xterm_bterms_proper{'t : Dform} : Nonterminal
declare xterm_bterms_list{'t : Dform} : Nonterminal
declare xterm_bterms_nonempty_list{'t : Dform} : Nonterminal

(*
 * A bterm is a single term, or \v1, ..., vn. term
 *)
production xterm_bterm{'t} <--
   xterm_term{'t}

production xterm_bterm{xbterm{| <H> >- 't |}} <--
   xterm_bterm_bind{xbterm{| <H> |}}; tok_dot; xterm_term{'t}

production xterm_bterm_bind{xbterm{| x: it |}} <--
   tok_id[x:s]

production xterm_bterm_bind{xbterm{| <H>; x: it |}} <--
   xterm_bterm_bind{xbterm{| <H> |}}; tok_comma; tok_id[x:s]

(*
 * Bterms are {...}
 *)
production xterm_bterms{xlist_sequent{||}} <--
   (* empty *)

production xterm_bterms{'t} <--
   xterm_bterms_proper{'t}

production xterm_bterms_proper{'t} <--
   tok_left_brace; xterm_bterms_list{'t}; tok_right_brace

production xterm_bterms_list{xlist_sequent{||}} <--
   (* empty *)

production xterm_bterms_list{'l} <--
   xterm_bterms_nonempty_list{'l}

production xterm_bterms_nonempty_list{xlist_sequent{| 't |}} <--
   xterm_bterm{'t}

production xterm_bterms_nonempty_list{xlist_sequent{| <H>; 't |}} <--
   xterm_bterms_nonempty_list{xlist_sequent{| <H> |}}; tok_semi; xterm_bterm{'t}

(*
 * The operator must be quoted.
 *)
production xterm_simple_term{xterm{'op; 'p; 't}} <--
   xterm_opname{'op}; xterm_params{'p}; xterm_bterms{'t}

production xterm_simple_term{xterm{xlist_sequent{| xopname[x:s] |}; xlist_sequent{||}; 't}} <--
   tok_id[x:s]; xterm_bterms_proper{'t}

(************************************************************************
 * Sequents.
 *)
declare typeclass parsed_hyps_exp

declare iform parsed_sequent{'e : Judgment} : Term

declare xterm_hyps{'e : parsed_hyps_exp} : Nonterminal
declare xterm_nonempty_hyps{'e : parsed_hyps_exp} : Nonterminal
declare xterm_hyp[x:s]{'e : 'a} : Nonterminal

declare sequent [parsed_hyps] { Term : Term >- Ignore } : parsed_hyps_exp

production xterm_simple_term{parsed_sequent{sequent { <H> >- 'e }}} <--
   tok_sequent; tok_left_brace; xterm_hyps{parsed_hyps{| <H> |}}; tok_turnstile; xterm_term{'e}; tok_right_brace

production xterm_hyps{parsed_hyps{||}} <--
   (* empty *)

production xterm_hyps{'e} <--
   xterm_nonempty_hyps{'e}

production xterm_nonempty_hyps{parsed_hyps{| x: 'e |}} <--
   xterm_hyp[x:s]{'e}

production xterm_nonempty_hyps{parsed_hyps{| <hyps>; x : 'e |}} <--
   xterm_nonempty_hyps{parsed_hyps{| <hyps> |}}; tok_semi; xterm_hyp[x:s]{'e}

production xterm_hyp[x:s]{'e} <--
   tok_id[x:s]; tok_colon; xterm_term{'e}

production xterm_hyp["_"]{'e} <--
   xterm_term{'e}

production xterm_hyp[""]{'c} <--
   xterm_context{'c}

(************************************************************************
 * Meta-terms.
 *)
declare xterm_meta_term{'t : MTerm} : Nonterminal

production xterm_meta_term{meta_theorem{'t}} <--
   xterm_term{'t}

production xterm_meta_term{meta_labeled[label:s]{'e}} <--
   tok_string[label:s]; tok_colon; xterm_meta_term{'e}

production xterm_meta_term{meta_implies{'e1; 'e2}} <--
   xterm_meta_term{'e1}; tok_longrightarrow; xterm_meta_term{'e2}

production xterm_meta_term{meta_iff{'e1; 'e2}} <--
   xterm_meta_term{'e1}; tok_longleftrightarrow; xterm_meta_term{'e2}

(* Allow a relaxed form of sequents in meta-terms *)
production xterm_meta_term{meta_theorem{sequent { <H> >- 'e }}} <--
   xterm_hyps{parsed_hyps{| <H> |}}; tok_turnstile; xterm_term{'e}

(************************************************************************
 * Toplevel productions.
 *)
declare xterm{'e : Term} : Nonterminal
declare xmterm{'e : MTerm} : Nonterminal
declare xrule{'e : MTerm} : Nonterminal
declare xrewrite{'e : MTerm} : Nonterminal
declare xquoterule{x. 'e : MTerm} : Nonterminal

parser xterm{'e} : xterm
parser xmterm{'e} : xterm
parser xrule{'e} : xterm
parser xrewrite{'e} : xterm
parser xquoterule{x. 'e} : xterm

production xterm{'e} <--
   xterm_term{'e}; tok_eof

production xmterm{'e} <--
   xterm_meta_term{'e}; tok_eof

production xrule{'e} <--
   xterm_meta_term{'e}; tok_eof

production xrewrite{'e} <--
   xterm_meta_term{'e}; tok_eof

production xquoterule{x. 'e} <--
   tok_id[x:s]; tok_dot; xterm_meta_term{'e}; tok_eof

(************************************************************************
 * Iforms.
 *)
iform unfold_xterm :
   xterm{'e}
   <-->
   'e

iform unfold_term_xmterm :
   xmterm{'e}
   <-->
   'e

iform unfold_term_xrule :
   xrule{'e}
   <-->
   'e

iform unfold_term_xrewrite :
   xrewrite{'e}
   <-->
   'e

iform unfold_term_xquoterule :
   xquoterule{x. 'e['x]}
   <-->
   xrulequote{x. 'e['x]}

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

(*
 * Sequents.
 *)
iform parsed_sequent :
   parsed_sequent{'e}
   <-->
   'e

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
