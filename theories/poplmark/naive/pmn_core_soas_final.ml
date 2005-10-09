(*
 * Close the simple Fsub theory.  That is, define the induction
 * principles.
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
extends Pmn_core_soas_terms
extends Pmn_core_soas_model
extends Itt_pairwise2
extends Itt_eta

open Basic_tactics

(************************************************************************
 * Define a model in ITT.
 *)
interactive ty_elim {| elim [] |} 'H : <:itt_rule<
    <H>; x: TyExp; <J[x]> >- C[top] -->
    <H>; x: TyExp; <J[x]>; v: TyVar >- C[type { ~v }] -->
    <H>; x: TyExp; <J[x]>; ty1: TyExp; ty2: TyExp; u: C[ty1]; v: C[ty2] >- C[type { ty1 -> ty2 }] -->
    <H>; x: TyExp; <J[x]>;
        ty1: TyExp; v: C[ty1];
        f: TyVar -> TyExp; all x: TyVar. C[f x]
        >- C[type { all x <: ty1. itt { f x } }] -->
    <H>; x: TyExp; <J[x]> >- C[x]
>>

interactive exp_elim {| elim [] |} 'H : <:itt_rule<
    <H>; x: Exp; <J[x]>; v: Var >- C[exp { ~v }] -->
    <H>; x: Exp; <J[x]>;
        e1: Exp; e2: Exp; u: C[e1]; v: C[e2] >- C[exp { e1 e2 }] -->
    <H>; x: Exp; <J[x]>;
        ty: TyExp;
        f: Var -> Exp; all x: Var. C[f x] >- C[exp { fun x: ty -> itt { f x } }] -->
    <H>; x: Exp; <J[x]>; e: Exp; u: C[e]; ty: TyExp >- C[exp { e{ty} }] -->
    <H>; x: Exp; <J[x]>;
        ty: TyExp;
        f: TyVar -> Exp; all x: TyVar. C[f x] >- C[exp { Fun x <: ty -> itt { f x } }] -->
    <H>; x: Exp; <J[x]> >- C[x]
>>

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
