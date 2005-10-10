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

(************************************************************************
 * Typeclasses for the different kinds of expressions in the theory.
 * Since we are going to be using ITT for reasoning, these typeclasses
 * are all trivially equal to Term (since ITT is untyped).
 *)
declare typeclass TyVar : Term
declare typeclass TyExp : Term
declare typeclass Var   : Term
declare typeclass Exp   : Term

declare rewrite TyVar <--> Term
declare rewrite TyExp <--> Term
declare rewrite Var   <--> Term
declare rewrite Exp   <--> Term
declare rewrite Prop  <--> Term

(************************************************************************
 * Type expressions.
 *
 * This definition is based on the use of second-order abstract syntax,
 * described in Despeyroux, Joëlle and Hirschowitz, Andre, "Higher-order
 * abstract syntax with induction in Coq", INRIA tech report RR-2292,
 * 1994, http://www.inria.fr/rrrt/rr-2292.html.
 *
 * To summarize, variables are constructed explicitly, and Lambda
 * abstractions are represented by functions over the "Var" type.
 *)

(*
 * Types.
 *)
declare TyTop  : TyExp
declare TyVar{'v : TyVar} : TyExp
declare TyFun{'ty_domain : TyExp; 'ty_range : TyExp} : TyExp
declare TyAll{'ty_bound : TyExp; x : TyVar. 'ty['x] : TyExp} : TyExp

(************************************************************************
 * Expressions.
 *)

(*
 * Variables.
 *)
declare Var{'v : Var} : Exp

(*
 * Normal abstraction and application.
 *)
declare Lambda{'ty_arg : TyExp; x : Var. 'e['x] : Exp} : Exp
declare Apply{'e1 : Exp; 'e2 : Exp} : Exp

(*
 * Type abstraction and application.
 *)
declare TyLambda{'ty_bound : TyExp; x : TyVar. 'e['x] : Exp} : Exp
declare TyApply{'e : Exp; 'ty_arg : TyExp} : Exp

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
declare tok_soas_type    : Terminal
declare tok_soas_exp     : Terminal
declare tok_soas_top     : Terminal
declare tok_soas_Var     : Terminal
declare tok_soas_Exp     : Terminal
declare tok_soas_TyVar   : Terminal
declare tok_soas_TyExp   : Terminal

declare tok_tilde        : Terminal
declare tok_dt           : Terminal
declare tok_st           : Terminal

lex_token itt : "itt"         --> tok_itt
lex_token itt : "soas_type"   --> tok_soas_type
lex_token itt : "soas_exp"    --> tok_soas_exp
lex_token itt : "soas_top"    --> tok_soas_top
lex_token itt : "soas_Var"    --> tok_soas_Var
lex_token itt : "soas_Exp"    --> tok_soas_Exp
lex_token itt : "soas_TyVar"  --> tok_soas_TyVar
lex_token itt : "soas_TyExp"  --> tok_soas_TyExp

lex_token itt : "~"      --> tok_tilde
lex_token itt : "<:"     --> tok_st
lex_token itt : "::"     --> tok_dt

lex_prec nonassoc [tok_st; tok_dt] = prec_in

(************************************************
 * Parsing.
 *)

(************************************************
 * Types.
 *)
declare typeclass parsed_type_exp -> TyExp

declare soas_type{'ty : TyExp} : Nonterminal
declare soas_simple_type{'ty : TyExp} : Nonterminal

production soas_simple_type{'e} <--
   itt_sovar{'e}

production soas_simple_type{'e} <--
   tok_quotation{'e}

production soas_simple_type{'e} <--
   tok_itt; tok_left_curly; itt_term{'e}; tok_right_curly

production soas_simple_type{TyVar{'v}} <--
   tok_tilde; tok_id[v:s]

production soas_simple_type{'e} <--
   tok_left_paren; soas_type{'e}; tok_right_paren

production soas_simple_type{TyTop} <--
   tok_soas_top

production soas_type{'e} <--
   soas_simple_type{'e}

production soas_type{TyFun{'ty1; 'ty2}} <--
   soas_type{'ty1}; tok_arrow; soas_type{'ty2}

production soas_type{TyAll{'ty1; v. 'ty2}} <--
   tok_all; tok_id[v:s]; tok_st; soas_type{'ty1}; tok_dot; soas_type{'ty2}

(************************************************
 * Expressions.
 *
 * We have the usual issue with application-by-concatenation.
 * Applications are only allowed on identifiers and parenthesized
 * expressions.
 *)
declare typeclass parsed_exp -> Exp

declare soas_exp{'e : Exp} : Nonterminal
declare soas_exp_apply{'e : Exp} : Nonterminal
declare soas_exp_simple{'e : Exp} : Nonterminal

(* Simple expressions that can be used in an application *)
production soas_exp_simple{'e} <--
   itt_sovar{'e}

production soas_exp_simple{'e} <--
   tok_quotation{'e}

production soas_exp_simple{'e} <--
   tok_itt; tok_left_curly; itt_term{'e}; tok_right_curly

production soas_exp_simple{Var{'v}} <--
   tok_tilde; tok_id[v:s]

production soas_exp_simple{'e} <--
   tok_left_paren; soas_exp{'e}; tok_right_paren

(* Applications *)
production soas_exp_apply{'e} <--
   soas_exp_simple{'e}

production soas_exp_apply{Apply{'e1; 'e2}} <--
   soas_exp_apply{'e1}; soas_exp_simple{'e2}

(* All expressions *)
production soas_exp{'e} <--
   soas_exp_apply{'e}

production soas_exp{Lambda{'ty; v. 'e}} <--
   tok_fun; tok_id[v:s]; tok_colon; soas_simple_type{'ty}; tok_arrow; soas_exp{'e}

production soas_exp{TyLambda{'ty; v. 'e}} <--
   tok_Fun; tok_id[v:s]; tok_st; soas_simple_type{'ty}; tok_arrow; soas_exp{'e}

production soas_exp{TyApply{'e; 'ty}} <--
   soas_exp{'e}; tok_left_curly; soas_type{'ty}; tok_right_curly

(************************************************
 * Propositions.
 *)
production itt_term{Var} <--
    tok_soas_Var

production itt_term{Exp} <--
    tok_soas_Exp

production itt_term{TyVar} <--
    tok_soas_TyVar

production itt_term{TyExp} <--
    tok_soas_TyExp

production itt_term{TyTop} <--
    tok_soas_top

production itt_term{'e} <--
    tok_soas_type; tok_left_curly; soas_type{'e}; tok_right_curly

production itt_term{'e} <--
    tok_soas_exp; tok_left_curly; soas_exp{'e}; tok_right_curly

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
