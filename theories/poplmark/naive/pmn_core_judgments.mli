(*
 * Sequent terms, propositions, and judgments.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2006 Mojave Group, Caltech
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
extends Pmn_core_terms

open Basic_tactics

(************************************************************************
 * Sequents.
 *
 * The type << Prop >> represents the "propositions" that appear
 * as the conclusion of a sequent.  We define a subtyping, and
 * a membership judgment.
 *
 * In a sequent, hypotheses are wrapped.
 * The << TyPower{'ty} >> is used in hypothesis lists to represent
 * subtyping assumptions, so @code{x : TyPower('ty)} means
 * @code{x <: 'ty}.
 *)
declare typeclass Prop -> Term

declare fsub_subtype{'ty1 : TyExp; 'ty2 : TyExp} : Prop
declare fsub_member{'e : Exp; 'ty : TyExp} : Prop

(*
 * XXX: JYH: for now, the filter has no idea what to do with
 * mta-subtyping rules, so we just use Perv!Judgment natively.
declare typeclass Judgment -> Perv!Judgment
 *)

declare typeclass KindExp -> Term
declare TyPower{'ty : TyExp} : KindExp

declare sequent [fsub] { Exp : TyExp | TyExp : KindExp >- Prop } : Judgment

(*
 * Wrapper terms for passing arguments to rules.
 *)
declare TyArg{'ty : TyExp}

(*
 * No extracts in this theory.
 *)
declare default_extract

(************************************************************************
 * Grammar.
declare tok_subtype   : Terminal

lex_token xterm : "<:"   --> tok_subtype

lex_prec nonassoc [tok_subtype] = prec_rel

declare iform parsed_tyexp{'e1} : TyExp

production xterm_term{fsub_subtype{parsed_tyexp{'e1}; parsed_tyexp{'e2}}} <--
   xterm_term{'e1}; tok_subtype; xterm_term{'e2}

iform reduce_parsed_tyexp :
   parsed_tyexp{'e1}
   <-->
   'e1
 *)

(*
 * -*-
 * Local Variables:
 * Fill-column: 120
 * End:
 * -*-
 * vim:ts=3:et:tw=120
 *)
