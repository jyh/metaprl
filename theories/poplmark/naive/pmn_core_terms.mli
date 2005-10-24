(*
 * Typed core language.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003-2005 Mojave Group, Caltech
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
extends Itt_theory
extends Itt_hoas_lang2

(************************************************************************
 * Types.
 *)
declare TyTop
declare TyFun{'ty_domain; 'ty_range}
declare TyAll{'ty_bound; x. 'ty['x]}

(************************************************************************
 * Expressions.
 *)

(*
 * Normal abstraction and application.
 *)
declare Lambda{'ty_arg; x. 'e['x]}
declare Apply{'e1; 'e2}

(*
 * Type abstraction and application.
 *)
declare TyLambda{'ty_bound; x. 'e['x]}
declare TyApply{'e; 'ty_arg}

(************************************************************************
 * The language.
 *)
declare FSubCore

(************************************************************************
 * The rest of this file defines a LALR(1) grammar for parsing
 * types and expressions in Fsub.  This isn't really necessary, since
 * we can always use the native MetaPRL term syntax to construct
 * terms in Fsub.  However, a custom grammar means that the definitions
 * are much more readable.
 *
 * This should be viewed with some degree of skepticism.  The grammar
 * could potentially mean that the terms you type are not what
 * you intend.  For instance, we could imagine that some adversary
 * defines a grammar where all propositions parse to "true".  There are
 * two counterarguments:
 *
 *    1. Display is defined separately, so the adversary would have
 *       to corrupt the display definitions too.
 *
 *    2. LALR(1) grammars are routine in PL.  If you are skeptical,
 *       you should be able to examine the grammar to see if it
 *       defines what you think.
 *)

(************************************************
 * Lexing.
 *)
declare tok_itt          : Terminal
declare tok_fsub         : Terminal
declare tok_top          : Terminal

declare tok_st           : Terminal

lex_token xterm : "fsub"        --> tok_fsub
lex_token xterm : "itt"         --> tok_itt
lex_token xterm : "top"         --> tok_top

lex_token xterm : "<:"          --> tok_st

lex_prec nonassoc [tok_st] = prec_equal

(************************************************
 * Types.
 *)
declare fsub_type{'ty} : Nonterminal
declare fsub_simple_type{'ty} : Nonterminal

production fsub_simple_type{'e} <--
   xterm_sovar{'e}

production fsub_simple_type{'e} <--
   tok_quotation{'e}

production fsub_simple_type{'e} <--
   tok_itt; tok_left_curly; xterm_term{'e}; tok_right_curly

production fsub_simple_type{'e} <--
   tok_left_paren; fsub_type{'e}; tok_right_paren

production fsub_simple_type{TyTop} <--
   tok_top

production fsub_type{'e} <--
   fsub_simple_type{'e}

production fsub_type{TyFun{'ty1; 'ty2}} <--
   fsub_type{'ty1}; tok_arrow; fsub_type{'ty2}

production fsub_type{TyAll{'ty1; v. 'ty2}} <--
   tok_all; tok_id[v:s]; tok_st; fsub_type{'ty1}; tok_dot; fsub_type{'ty2}

(************************************************
 * Expressions.
 *
 * We have the usual issue with application-by-concatenation.
 * Applications are only allowed on identifiers and parenthesized
 * expressions.
 *)
declare fsub_exp{'e} : Nonterminal
declare fsub_exp_apply{'e} : Nonterminal
declare fsub_exp_simple{'e} : Nonterminal

(* Simple expressions that can be used in an application *)
production fsub_exp_simple{'e} <--
   xterm_sovar{'e}

production fsub_exp_simple{'e} <--
   tok_quotation{'e}

production fsub_exp_simple{'e} <--
   tok_itt; tok_left_curly; xterm_term{'e}; tok_right_curly

production fsub_exp_simple{'e} <--
   tok_left_paren; fsub_exp{'e}; tok_right_paren

(* Applications *)
production fsub_exp_apply{'e} <--
   fsub_exp_simple{'e}

production fsub_exp_apply{Apply{'e1; 'e2}} <--
   fsub_exp_apply{'e1}; fsub_exp_simple{'e2}

(* All expressions *)
production fsub_exp{'e} <--
   fsub_exp_apply{'e}

production fsub_exp{Lambda{'ty; v. 'e}} <--
   tok_fun; tok_id[v:s]; tok_colon; fsub_simple_type{'ty}; tok_arrow; fsub_exp{'e}

production fsub_exp{TyLambda{'ty; v. 'e}} <--
   tok_Fun; tok_id[v:s]; tok_st; fsub_simple_type{'ty}; tok_arrow; fsub_exp{'e}

production fsub_exp{TyApply{'e; 'ty}} <--
   fsub_exp{'e}; tok_left_curly; fsub_type{'ty}; tok_right_curly

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
