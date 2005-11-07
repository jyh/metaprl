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
extends Itt_hoas_theory

open Basic_tactics

(************************************************************************
 * Types.
 *)
declare typeclass TyExp -> Term

declare TyTop : TyExp
declare TyFun{'ty_domain : TyExp; 'ty_range : TyExp} : TyExp
declare TyAll{'ty_bound : TyExp; x : TyExp. 'ty['x] : TyExp} : TyExp

(************************************************************************
 * Expressions.
 *)
declare typeclass Exp -> Term

(*
 * Normal abstraction and application.
 *)
declare Lambda{'ty_arg : TyExp; x : Exp. 'e['x] : Exp} : Exp
declare Apply{'e1 : Exp; 'e2 : Exp} : Exp

(*
 * Type abstraction and application.
 *)
declare TyLambda{'ty_bound : TyExp; x : TyExp. 'e['x] : Exp} : Exp
declare TyApply{'e : Exp; 'ty_arg : TyExp} : Exp

(************************************************************************
 * Judgments.
 *)
declare typeclass Prop -> Term

declare fsub_subtype{'ty1 : TyExp; 'ty2 : TyExp} : Prop
declare fsub_member{'e : Exp; 'ty : TyExp} : Prop

(************************************************************************
 * Sequents.
 *
 * Hypotheses are wrapped.  The << TyVal{'ty} >> represents the
 * programs that have type << 'ty >>.
 *
 * The << TyPower{'ty} >> is used in hypothesis lists to represent
 * subtyping assumptions.
 *)
declare typeclass Judgment -> Perv!Judgment

declare typeclass Hyp -> Ty

declare typeclass TyVal : Hyp -> Term
declare typeclass TyPower : Hyp -> Term

declare TyVal{'ty : TyExp} : TyVal
declare TyPower{'ty : TyExp} : TyPower

(*
 * Sequents have dependent types.
 *)
declare type TyElem{'a : Ty} : Ty

declare rewrite TyElem{TyVal} <--> Exp
declare rewrite TyElem{TyPower} <--> TyExp

declare sequent [fsub] { exst a: Hyp. TyElem{'a} : 'a >- Prop } : Judgment

(*
 * Provability.
 *)
declare Provable{'e}

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
declare tok_itt            : Terminal
declare tok_fsub           : Terminal
declare tok_top            : Terminal

declare tok_st             : Terminal
declare tok_colon_in_colon : Terminal

lex_token xterm : "fsub"        --> tok_fsub
lex_token xterm : "itt"         --> tok_itt
lex_token xterm : "top"         --> tok_top

lex_token xterm : "<:"          --> tok_st
lex_token xterm : ":in:" --> tok_colon_in_colon

lex_prec nonassoc [tok_st] = prec_equal
lex_prec nonassoc [tok_colon_in_colon] = prec_in

(************************************************************************
 * Atomic terms.
 *)
declare fsub_atomic{'e : 'a} : Nonterminal

production fsub_atomic{'e} <--
   xterm_sovar{'e}

production fsub_atomic{'e} <--
   tok_quotation{'e}

production fsub_atomic{'e} <--
   tok_itt; tok_left_brace; xterm_term{'e}; tok_right_brace

(************************************************
 * Expressions.
 *
 * We have the usual issue with application-by-concatenation.
 * Applications are only allowed on identifiers and parenthesized
 * expressions.
 *)
declare fsub_exp{'e : 'a} : Nonterminal
declare fsub_exp_apply{'e : 'a} : Nonterminal
declare fsub_exp_simple{'e : 'a} : Nonterminal

(* Simple expressions that can be used in an application *)
production fsub_exp_simple{'e} <--
   fsub_atomic{'e}

production fsub_exp_simple{'e} <--
   tok_left_paren; fsub_exp{'e}; tok_right_paren

(* Applications *)
production fsub_exp_apply{'e} <--
   fsub_exp_simple{'e}

production fsub_exp_apply{Apply{'e1; 'e2}} <--
   fsub_exp_apply{'e1}; fsub_exp_simple{'e2}

production fsub_exp{'e} <--
   fsub_exp_apply{'e}

(* Type expressions *)
production fsub_exp{TyTop} <--
   tok_top

production fsub_exp{TyFun{'ty1; 'ty2}} <--
   fsub_exp{'ty1}; tok_arrow; fsub_exp{'ty2}

production fsub_exp{TyAll{'ty1; v. 'ty2}} <--
   tok_all; tok_id[v:s]; tok_st; fsub_exp{'ty1}; tok_dot; fsub_exp{'ty2}

(* Normal expressions *)
production fsub_exp{Lambda{'ty; v. 'e}} <--
   tok_fun; tok_id[v:s]; tok_colon; fsub_exp{'ty}; tok_arrow; fsub_exp{'e}

production fsub_exp{TyLambda{'ty; v. 'e}} <--
   tok_Fun; tok_id[v:s]; tok_st; fsub_exp{'ty}; tok_arrow; fsub_exp{'e}

production fsub_exp{TyApply{'e; 'ty}} <--
   fsub_exp{'e}; tok_left_brace; fsub_exp{'ty}; tok_right_brace

(************************************************************************
 * Integrate into the ITT language.
 *)
production xterm_term{'e} <--
   tok_fsub; tok_left_brace; fsub_exp{'e}; tok_right_brace

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
