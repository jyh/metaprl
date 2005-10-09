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
    <H>; x: soas_TyExp; <J[x]> >- C[soas_top] -->
    <H>; x: soas_TyExp; <J[x]>; v: soas_TyVar >- C[soas_type { ~v }] -->
    <H>; x: soas_TyExp; <J[x]>; ty1: soas_TyExp; ty2: soas_TyExp; u: C[ty1]; v: C[ty2] >- C[soas_type { ty1 -> ty2 }] -->
    <H>; x: soas_TyExp; <J[x]>;
        ty1: soas_TyExp; v: C[ty1];
        f: soas_TyVar -> soas_TyExp; all x: soas_TyVar. C[f x]
        >- C[soas_type { all x <: ty1. itt { f x } }] -->
    <H>; x: soas_TyExp; <J[x]> >- C[x]
>>

interactive exp_elim {| elim [] |} 'H : <:itt_rule<
    <H>; x: soas_Exp; <J[x]>; v: soas_Var >- C[soas_exp { ~v }] -->
    <H>; x: soas_Exp; <J[x]>;
        e1: soas_Exp; e2: soas_Exp; u: C[e1]; v: C[e2] >- C[soas_exp { e1 e2 }] -->
    <H>; x: soas_Exp; <J[x]>;
        ty: soas_TyExp;
        f: soas_Var -> soas_Exp; all x: soas_Var. C[f x] >- C[soas_exp { fun x: ty -> itt { f x } }] -->
    <H>; x: soas_Exp; <J[x]>; e: soas_Exp; u: C[e]; ty: soas_TyExp >- C[soas_exp { e{ty} }] -->
    <H>; x: soas_Exp; <J[x]>;
        ty: soas_TyExp;
        f: soas_TyVar -> soas_Exp; all x: soas_TyVar. C[f x] >- C[soas_exp { Fun x <: ty -> itt { f x } }] -->
    <H>; x: soas_Exp; <J[x]> >- C[x]
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
