(*
 * Typed AST.
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
extends Itt_hoas_util

open Basic_tactics

open Itt_dfun
open Itt_logic

(************************************************************************
 * Display forms.
 *)
dform top_df : <:xterm< fsub type [d] { top } >> =
   `"Top[" slot{'d} `"]"

dform ty_fun_df : parens :: "prec"[prec_fun] :: <:xterm< fsub type [d] { ty1 -> ty2 } >> =
   szone pushm[3] slot{'ty1} `" ->[" slot{'d} `"]" hspace slot{'ty2} popm ezone

dform ty_all_df : parens :: "prec"[prec_quant] :: <:xterm< fsub type [d] { all x <: ty1. ty2 } >> =
   szone pushm[3] `"all[" slot{'d} `"] " slot{'x} `" <: " slot{'ty1} `"." hspace slot{'ty2} popm ezone

dform lambda_df : parens :: "prec"[prec_lambda] :: <:xterm< fsub [d] { fun x : ty -> e } >> =
   szone pushm[3] `"fun[" slot{'d} `"] " slot{'x} `" : " slot{'ty} `" ->" hspace slot{'e} popm ezone

dform apply_df : parens :: "prec"[prec_apply] :: <:xterm< fsub [d] { e1 e2 } >> =
   szone pushm[3] slot{'e1} `" @[" slot{'d} `"]" hspace slot{'e2} popm ezone

dform ty_lambda_df : parens :: "prec"[prec_lambda] :: <:xterm< fsub [d] { Fun x <: ty -> e } >> =
   szone pushm[3] `"Fun[" slot{'d} `"] " slot{'x} `" <: " slot{'ty} `" ->" hspace slot{'e} popm ezone

dform ty_apply_df : parens :: "prec"[prec_apply] :: <:xterm< fsub [d] { e{ty} } >> =
   szone pushm[3] slot{'e} `"@[" slot{'d} `"]{" slot{'ty} `"}" popm ezone

(************************************************************************
 * Type expressions.
 *)

(*
 * The language predicate.
 *)
define unfold_isTyExp : isTyExp{'e} <--> <:xterm<
   (fix is_ty_exp e ->
      dest_bterm e with
         l, r -> "true"
       | d, o, s ->
            if is_same_op{o; $"TyTop"} then
               "true"
            else if is_same_op{o; $TyFun{ty1; ty2}} then
               is_ty_exp nth{s; 0} && is_ty_exp nth{s; 1}
            else if is_same_op{o; $TyAll{ty1; x. ty2[x]}} then
               is_ty_exp nth{s; 0} && is_ty_exp nth{s; 1}
            else
               "false") e
>>

let fold_isTyExp = makeFoldC << isTyExp{'e} >> unfold_isTyExp

interactive isTyExp_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "BTerm" -->
   <H> >- isTyExp{e} Type
>>

(*
 * Some reduction rules for the terms.
 *)
interactive_rw is_ty_exp_ty_top {| reduce |} : <:xrewrite<
   d IN "nat" -->
   isTyExp{fsub type[d] { top }}
   <-->
   "true"
>>

interactive_rw is_ty_exp_ty_fun {| reduce |} : <:xrewrite<
   d IN "nat" -->
   t1 IN "BTerm" -->
   t2 IN "BTerm" -->
   bdepth{t1} = d in "nat" -->
   bdepth{t2} = d in "nat" -->
   isTyExp{fsub type[d] { t1 -> t2 }}
   <-->
   isTyExp{t1} && isTyExp{t2}
>>

interactive_rw is_ty_exp_ty_all {| reduce |} : <:xrewrite<
   d IN "nat" -->
   t1 IN "BTerm" -->
   bind{x. t2[x]} IN "BTerm" -->
   bdepth{t1} = d in "nat" -->
   bdepth{t2["dummy"]} = d in "nat" -->
   isTyExp{fsub type[d] { all x <: t1. t2[x] }}
   <-->
   isTyExp{t1} && isTyExp{bind{x. t2[x]}}
>>

interactive_rw is_ty_exp_false : <:xrewrite<
   d IN "nat" -->
   op IN "Operator" -->
   subterms IN list{"BTerm"} -->
   compatible_shapes{d; shape{op}; subterms} -->
   "not"{op = $"TyTop" in "Operator"} -->
   "not"{op = $TyFun{ty1; ty2} in "Operator"} -->
   "not"{op = $TyAll{ty1; x. ty2} in "Operator"} -->
   isTyExp{mk_bterm{d; op; subterms}}
   <-->
   "false"
>>

(*
 * The type of type expressions.
 *)
define unfold_TyExp : TyExp <--> <:xterm<
   { e: "BTerm" | isTyExp{e} }
>>

interactive ty_exp_wf {| intro [] |} : <:xrule<
   <H> >- "TyExp" Type
>>

interactive replace_ty_exp 'H : <:xrule<
   "wf" : <H>; e: "BTerm"; <J[e]> >- squash{isTyExp{e}} -->
   <H>; e: "TyExp"; <J[e]> >- C[e] -->
   <H>; e: "BTerm"; <J[e]> >- C[e]
>>

(*
 * Derive a more useful induction principle.
 *)
interactive ty_exp_elim3 {| elim [] |} 'H : <:xrule<
   "base" : <H>; e: TyExp{}; <J[e]>; v: Var{} >- P[v] -->

   "base" : <H>; e: TyExp{}; <J[e]>; d: nat{} >- P[fsub type[d] { top }] -->

   "step" : <H>; e: TyExp{}; <J[e]>; t1: TyExp{}; t2: TyExp{}; P[t1]; P[t2];
      bdepth{t1} = bdepth{t2} in nat{} >- P[fsub type[bdepth{t1}] { t1 -> t2 }] -->

   "step" : <H>; e: TyExp{}; <J[e]>; t1: TyExp{}; t2: TyExp{}; P[t1]; P[t2];
      bdepth{t2} = bdepth{t1} +@ 1 in nat{}
      >- P[fsub type[bdepth{t1}] { all x <: t1. itt { subst{t2; x} } }] -->

   <H>; e: TyExp{}; <J[e]> >- P[e]
>>

(************************************************************************
 * Expressions.
 *)

(*
 * The language predicate.
 *)
define unfold_isExp : isExp{'e} <--> <:xterm<
   (fix is_exp e ->
      dest_bterm e with
         l, r -> "true"
       | d, o, s ->
            if is_same_op{o; $Apply{e1; e2}} then
               is_exp nth{s; 0} && is_exp nth{s; 1}
            else if is_same_op{o; $Lambda{ty; x. e}} then
               isTyExp{nth{s; 0}} && is_exp nth{s; 1}
            else if is_same_op{o; $TyApply{e1; e2}} then
               is_exp nth{s; 0} && isTyExp{nth{s; 1}}
            else if is_same_op{o; $TyLambda{ty; x. e}} then
               isTyExp{nth{s; 0}} && is_exp nth{s; 1}
            else
               "false") e
>>

let fold_isExp = makeFoldC << isExp{'e} >> unfold_isExp

interactive isExp_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "BTerm" -->
   <H> >- isExp{e} Type
>>

(*
 * Some reduction rules for the terms.
 *)
interactive_rw is_exp_apply {| reduce |} : <:xrewrite<
   d IN "nat" -->
   e1 IN "BTerm" -->
   e2 IN "BTerm" -->
   bdepth{e1} = d in "nat" -->
   bdepth{e2} = d in "nat" -->
   isExp{fsub[d] { e1 e2 }}
   <-->
   isExp{e1} && isExp{e2}
>>

interactive_rw is_exp_lambda {| reduce |} : <:xrewrite<
   d IN "nat" -->
   ty IN "BTerm" -->
   bind{x. e[x]} IN "BTerm" -->
   bdepth{ty} = d in "nat" -->
   bdepth{e["dummy"]} = d in "nat" -->
   isExp{fsub[d] { fun x: ty -> e[x] }}
   <-->
   isTyExp{ty} && isExp{bind{x. e[x]}}
>>

interactive_rw is_exp_ty_apply {| reduce |} : <:xrewrite<
   d IN "nat" -->
   e IN "BTerm" -->
   ty IN "BTerm" -->
   bdepth{e} = d in "nat" -->
   bdepth{ty} = d in "nat" -->
   isExp{fsub[d] { e{ty} }}
   <-->
   isExp{e} && isTyExp{ty}
>>

interactive_rw is_exp_ty_lambda {| reduce |} : <:xrewrite<
   d IN "nat" -->
   ty IN "BTerm" -->
   bind{x. e[x]} IN "BTerm" -->
   bdepth{ty} = d in "nat" -->
   bdepth{e["dummy"]} = d in "nat" -->
   isExp{fsub[d] { Fun x <: ty -> e[x] }}
   <-->
   isTyExp{ty} && isExp{bind{x. e[x]}}
>>

interactive_rw is_exp_false : <:xrewrite<
   d IN "nat" -->
   op IN "Operator" -->
   subterms IN list{"BTerm"} -->
   compatible_shapes{d; shape{op}; subterms} -->
   "not"{op = $Apply{e1; e2} in "Operator"} -->
   "not"{op = $Lambda{ty; x. e} in "Operator"} -->
   "not"{op = $TyApply{e1; e2} in "Operator"} -->
   "not"{op = $TyLambda{ty; x. e} in "Operator"} -->
   isExp{mk_bterm{d; op; subterms}}
   <-->
   "false"
>>

(*
 * The type of type expressions.
 *)
define unfold_Exp : Exp <--> <:xterm<
   { e: "BTerm" | isExp{e} }
>>

interactive exp_wf {| intro [] |} : <:xrule<
   <H> >- "Exp" Type
>>

interactive replace_exp 'H : <:xrule<
   "wf" : <H>; e: "BTerm"; <J[e]> >- squash{isExp{e}} -->
   <H>; e: "Exp"; <J[e]> >- C[e] -->
   <H>; e: "BTerm"; <J[e]> >- C[e]
>>

(*
 * Derive a more useful induction principle.
 *)
interactive exp_elim2 {| elim [] |} 'H : <:xrule<
   "base" : <H>; e: Exp{}; <J[e]>; v: Var{} >- P[v] -->

   "step" : <H>; e: Exp{}; <J[e]>; e1: Exp{}; e2: Exp{}; P[e1]; P[e2];
      bdepth{e1} = bdepth{e2} in nat{} >- P[fsub[bdepth{e1}] { e1 e2 }] -->

   "step" : <H>; e: Exp{}; <J[e]>; ty: TyExp{}; e1: Exp{}; P[e1];
      bdepth{e1} = bdepth{ty} +@ 1 in nat{}
      >- P[fsub[bdepth{ty}] { fun x: ty -> itt{ subst{e1; x} } }] -->

   "step" : <H>; e: Exp{}; <J[e]>; e1: Exp{}; ty: TyExp{}; P[e1];
      bdepth{e1} = bdepth{ty} in nat{} >- P[fsub[bdepth{e1}] { e1{ty} }] -->

   "step" : <H>; e: Exp{}; <J[e]>; ty: TyExp{}; e1: Exp{}; P[e1];
      bdepth{e1} = bdepth{ty} +@ 1 in nat{}
      >- P[fsub[bdepth{ty}] { Fun x <: ty -> itt { subst{e1; x} } }] -->

   <H>; e: Exp{}; <J[e]> >- P[e]
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
