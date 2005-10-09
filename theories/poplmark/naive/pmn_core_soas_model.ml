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

open Basic_tactics

(************************************************************************
 * Define a model in ITT.
 *)

(*
 * Types are a 4-part recursive type.
 *)
prim_rw unfold_ty_var_type :
    TyVar
    <-->
    int

prim_rw unfold_ty_exp :
    TyExp
    <-->
    srec{TyExp.
        unit                         (* Top *)
      + TyVar                        (* Var *)
      + 'TyExp * 'TyExp              (* TyFun *)
      + 'TyExp * (TyVar -> 'TyExp)}  (* TyAll *)

prim_rw unfold_ty_top :
    TyTop
    <-->
    inl{it}

prim_rw unfold_ty_var :
    TyVar{'v}
    <-->
    inr{inl{'v}}

prim_rw unfold_ty_fun :
    TyFun{'ty1; 'ty2}
    <-->
    inr{inr{inl{pair{'ty1; 'ty2}}}}

prim_rw unfold_ty_all :
    TyAll{'ty1; x. 'ty2['x]}
    <-->
    inr{inr{inr{pair{'ty1; lambda{x. 'ty2['x]}}}}}

let fold_ty_var_type = makeFoldC << TyVar >> unfold_ty_var_type
let fold_ty_exp      = makeFoldC << TyExp >> unfold_ty_exp
let fold_ty_top      = makeFoldC << TyTop >> unfold_ty_top
let fold_ty_var      = makeFoldC << TyVar{'v} >> unfold_ty_var
let fold_ty_fun      = makeFoldC << TyFun{'e1; 'e2} >> unfold_ty_fun
let fold_ty_all      = makeFoldC << TyAll{'ty1; x. 'ty2['x]} >> unfold_ty_all

(*
 * Expressions are a 5-part recursive type.
 *)
prim_rw unfold_var_type :
    Var
    <-->
    int

prim_rw unfold_exp :
    Exp
    <-->
    srec{Exp.
        Var                           (* Var *)
      + 'Exp * 'Exp                   (* Apply *)
      + TyExp * (Var -> 'Exp)         (* Lambda *)
      + 'Exp * TyExp                  (* TyApply *)
      + TyExp * (TyVar -> 'Exp)}      (* TyLambda *)

prim_rw unfold_var :
    Var{'v}
    <-->
    inl{'v}

prim_rw unfold_apply :
    Apply{'e1; 'e2}
    <-->
    inr{inl{pair{'e1; 'e2}}}

prim_rw unfold_lambda :
    Lambda{'ty; x. 'e['x]}
    <-->
    inr{inr{inl{pair{'ty; lambda{x. 'e['x]}}}}}

prim_rw unfold_ty_apply :
    TyApply{'e; 'ty}
    <-->
    inr{inr{inr{inl{pair{'e; 'ty}}}}}

prim_rw unfold_ty_lambda :
    TyLambda{'ty; x. 'e['x]}
    <-->
    inr{inr{inr{inr{pair{'ty; lambda{x. 'e['x]}}}}}}

let fold_var_type = makeFoldC << Var >> unfold_var_type
let fold_exp = makeFoldC << Exp >> unfold_exp
let fold_var = makeFoldC << Var{'v} >> unfold_var
let fold_apply = makeFoldC << Apply{'e1; 'e2} >> unfold_apply
let fold_lambda = makeFoldC << Lambda{'ty; x. 'e['x]} >> unfold_lambda
let fold_ty_apply = makeFoldC << TyApply{'e; 'ty} >> unfold_ty_apply
let fold_ty_lambda = makeFoldC << TyLambda{'ty; x. 'e['x]} >> unfold_ty_lambda

(************************************************************************
 * Well-formedness lemmas.
 *)
interactive ty_var_type_wf1 {| intro [] |} :
    sequent { <H> >- TyVar in univ[1:l] }

interactive ty_var_type_wf2 {| intro [] |} :
    sequent { <H> >- Itt_equal!"type"{TyVar} }

interactive ty_exp_wf {| intro [] |} :
    sequent { <H> >- TyExp in univ[1:l] }

interactive ty_exp_wf_type {| intro [] |} :
    sequent { <H> >- "type"{TyExp} }

interactive ty_top_wf {| intro [] |} :
    sequent { <H> >- TyTop in TyExp }

interactive ty_var_wf {| intro [] |} :
    sequent { <H> >- 'v in TyVar } -->
    sequent { <H> >- TyVar{'v} in TyExp }

interactive ty_fun_wf {| intro [] |} :
    sequent { <H> >- 'ty1 in TyExp } -->
    sequent { <H> >- 'ty2 in TyExp } -->
    sequent { <H> >- TyFun{'ty1; 'ty2} in TyExp }

interactive ty_all_wf {| intro [] |} :
    sequent { <H> >- 'ty in TyExp } -->
    sequent { <H>; x : TyVar >- 'e['x] in TyExp } -->
    sequent { <H> >- TyAll{'ty; x. 'e['x]} in TyExp }

interactive var_type_wf1 {| intro [] |} :
    sequent { <H> >- Var in univ[1:l] }

interactive var_type_wf2 {| intro [] |} :
    sequent { <H> >- "type"{Var} }

interactive exp_wf1 {| intro [] |} :
    sequent { <H> >- Exp in univ[1:l] }

interactive exp_wf2 {| intro [] |} :
    sequent { <H> >- "type"{Exp} }

interactive var_wf {| intro [] |} :
    sequent { <H> >- 'v in Var } -->
    sequent { <H> >- Var{'v} in Exp }

interactive apply_wf {| intro [] |} :
    sequent { <H> >- 'e1 in Exp } -->
    sequent { <H> >- 'e2 in Exp } -->
    sequent { <H> >- Apply{'e1; 'e2} in Exp }

interactive lambda_wf {| intro [] |} :
    sequent { <H> >- 'ty in TyExp } -->
    sequent { <H>; x : Var >- 'e['x] in Exp } -->
    sequent { <H> >- Lambda{'ty; x. 'e['x]} in Exp }

interactive ty_apply_wf {| intro [] |} :
    sequent { <H> >- 'e in Exp } -->
    sequent { <H> >- 'ty in TyExp } -->
    sequent { <H> >- TyApply{'e; 'ty} in Exp }

interactive ty_lambda_wf {| intro [] |} :
    sequent { <H> >- 'ty in TyExp } -->
    sequent { <H>; x: TyVar >- 'e['x] in Exp } -->
    sequent { <H> >- TyLambda{'ty; x. 'e['x]} in Exp }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
