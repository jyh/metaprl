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
 * We'll define the type judgments manually.
 *)
declare sequent [fsub] { Term : Term >- Term } : Term

(*
 * -*-
 * Local Variables:
 * Fill-column: 120
 * End:
 * -*-
 * vim:ts=3:et:tw=120
 *)
