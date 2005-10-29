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
extends Itt_hoas_lang2

open Basic_tactics

open Itt_dfun
open Itt_logic

(************************************************************************
 * The reflected language.
 *)
define unfold_fsub_core : FSubCore <--> <:xterm<
   Lang [$TyTop{};
         $TyFun{ty1; ty2};
         $TyAll{ty1; x. ty2};
         $Lambda{ty; x. e};
         $Apply{e1; e2};
         $TyLambda{ty; x. e};
         $TyApply{e; ty}]
>>

let fold_fsub_core = makeFoldC << FSubCore >> unfold_fsub_core

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
 * Basic well-formedness.
 *)
interactive fsub_core_wf : <:xrule<
   <H> >- "FSubCore" Type
>>

interactive top_wf : <:xrule<
   <H> >- d IN "nat" -->
   <H> >- fsub type [d] { top } IN "FSubCore"
>>

interactive ty_fun_wf : <:xrule<
   <H> >- "bdepth"{ty1} = d in "nat" -->
   <H> >- "bdepth"{ty2} = d in "nat" -->
   <H> >- ty1 IN "FSubCore" -->
   <H> >- ty2 IN "FSubCore" -->
   <H> >- fsub type [d] { ty1 -> ty2 } IN "FSubCore"
>>

interactive ty_all_wf : <:xrule<
   <H> >- "bdepth"{ty1} = d in "nat" -->
   <H> >- "bdepth"{ty2["dummy"]} = d in "nat" -->
   <H> >- ty1 IN "FSubCore" -->
   <H> >- "bind"{x. ty2[x]} IN "FSubCore" -->
   <H> >- fsub type [d] { all x <: ty1. ty2[x] } IN "FSubCore"
>>

interactive lambda_wf : <:xrule<
   <H> >- "bdepth"{ty} = d in "nat" -->
   <H> >- "bdepth"{e["dummy"]} = d in "nat" -->
   <H> >- ty IN "FSubCore" -->
   <H> >- "bind"{x. e[x]} IN "FSubCore" -->
   <H> >- fsub [d] { fun x : ty -> e[x] } IN "FSubCore"
>>

interactive apply_wf : <:xrule<
   <H> >- "bdepth"{e1} = d in "nat" -->
   <H> >- "bdepth"{e2} = d in "nat" -->
   <H> >- e1 IN "FSubCore" -->
   <H> >- e2 IN "FSubCore" -->
   <H> >- fsub [d] { e1 e2 } IN "FSubCore"
>>

interactive ty_lambda_wf : <:xrule<
   <H> >- "bdepth"{ty} = d in "nat" -->
   <H> >- "bdepth"{e["dummy"]} = d in "nat" -->
   <H> >- ty IN "FSubCore" -->
   <H> >- "bind"{x. e[x]} IN "FSubCore" -->
   <H> >- fsub [d] { Fun x <: ty -> e[x] } IN "FSubCore"
>>

interactive ty_apply_wf : <:xrule<
   <H> >- "bdepth"{e1} = d in "nat" -->
   <H> >- "bdepth"{e2} = d in "nat" -->
   <H> >- e1 IN "FSubCore" -->
   <H> >- e2 IN "FSubCore" -->
   <H> >- fsub [d] { e1{e2} } IN "FSubCore"
>>

(************************************************************************
 * Induction principle for the entire language.
 *)
interactive fsub_core_elim {| elim [] |} 'H : <:xrule<
   <H>; e: FSubCore{}; <J[e]>; v: Var{} >- P[v] -->

   <H>; e: FSubCore{}; <J[e]>; d: nat{} >- P[fsub type[d] { top }] -->

   <H>; e: FSubCore{}; <J[e]>; t1: FSubCore{}; t2: FSubCore{}; P[t1]; P[t2];
      bdepth{t1} = bdepth{t2} in nat{} >- P[fsub type[bdepth{t1}] { t1 -> t2 }] -->

   <H>; e: FSubCore{}; <J[e]>; t1: FSubCore{}; t2: FSubCore{}; P[t1]; P[t2];
      bdepth{t2} = bdepth{t1} +@ 1 in nat{}
      >- P[fsub type[bdepth{t1}] { all x <: t1. itt { subst{t2; x} } }] -->

   <H>; e: FSubCore{}; <J[e]>; t1: FSubCore{}; e1: FSubCore{}; P[t1]; P[e1];
      bdepth{e1} = bdepth{t1} +@ 1 in nat{}
      >- P[fsub [bdepth{t1}] { fun x: t1 -> itt { subst{e1; x} } }] -->

   <H>; e: FSubCore{}; <J[e]>; e1: FSubCore{}; e2: FSubCore{}; P[e1]; P[e2];
      bdepth{e1} = bdepth{e2} in nat{} >- P[fsub [bdepth{e1}] { e1 e2 }] -->

   <H>; e: FSubCore{}; <J[e]>; t1: FSubCore{}; e1: FSubCore{}; P[t1]; P[e1];
      bdepth{e1} = bdepth{t1} +@ 1 in nat{}
      >- P[fsub [bdepth{t1}] { Fun x <: t1 -> itt { subst{e1; x} } }] -->

   <H>; e: FSubCore{}; <J[e]>; e1: FSubCore{}; t1: FSubCore{}; P[e1]; P[t1];
      bdepth{e1} = bdepth{t1} in nat{} >- P[fsub [bdepth{e1}] { e1{t1} }] -->

   <H>; e: FSubCore{}; <J[e]> >- P[e]
>>

(************************************************************************
 * Define a generic induction combinator.
 *)
interactive bdepth_wf {| intro [intro_typeinf << 'e >>] |} FSubCore :
   [wf] sequent { <H> >- 'e in FSubCore } -->
   sequent { <H> >- bdepth{'e} in nat }

interactive bdepth_wf_int {| intro [intro_typeinf << 'e >>] |} FSubCore :
   [wf] sequent { <H> >- 'e in FSubCore } -->
   sequent { <H> >- bdepth{'e} in int }

interactive_rw bind_eta :
   'e in FSubCore -->
   bdepth{'e} > 0 -->
   bind{x. subst{'e; 'x}}
   <-->
   'e

interactive fsub_core_bterm {| intro [intro_typeinf << 'e >>] |} FSubCore :
   sequent { <H> >- 'e in FSubCore } -->
   sequent { <H> >- 'e in BTerm }

define unfold_dest_fsub_exp :
   dest_exp{'e;
      x. 'base['x];
      'ty_top;
      ty1, ty2. 'ty_fun['ty1; 'ty2];
      ty1, ty2. 'ty_all['ty1; 'ty2];
      ty, e. 'lam['ty; 'e];
      e1, e2. 'apply['e1; 'e2];
      ty, e. 'ty_lam['ty; 'e];
      e, ty. 'ty_apply['e; 'ty]} <--> <:xterm<
   dest_bterm e with
      l, r -> base[var{l; r}]
    | d, o, s ->
      if is_same_op{o; $TyTop{}} then
         ty_top
      else if is_same_op{o; $TyFun{ty1; ty2}} then
         ty_fun[nth{s; 0}; nth{s; 1}]
      else if is_same_op{o; $TyAll{ty1; x. ty2}} then
         ty_all[nth{s; 0}; nth{s; 1}]
      else if is_same_op{o; $Lambda{ty; x. e}} then
         lam[nth{s; 0}; nth{s; 1}]
      else if is_same_op{o; $Apply{e1; e2}} then
         apply[nth{s; 0}; nth{s; 1}]
      else if is_same_op{o; $TyLambda{ty; x. e}} then
         ty_lam[nth{s; 0}; nth{s; 1}]
      else if is_same_op{o; $TyApply{e; ty}} then
         ty_apply[nth{s; 0}; nth{s; 1}]
      else
         it{}
>>

interactive_rw dest_fsub_exp_var {| reduce |} :
   'l in nat -->
   'r in nat -->
<:xrewrite<
   dest_exp{var{l; r};
      x. base[x];
      ty_top;
      ty1, ty2. ty_fun[ty1; ty2];
      ty1, ty2. ty_all[ty1; ty2];
      ty, e. lam[ty; e];
      e1, e2. apply[e1; e2];
      ty, e. ty_lam[ty; e];
      e, ty. ty_apply[e; ty]}
   <-->
   base[var{l; r}]
>>

interactive_rw dest_fsub_exp_top {| reduce |} :
   'd in nat -->
<:xrewrite<
   dest_exp{fsub type[d] { top };
      x. base[x];
      ty_top;
      ty1, ty2. ty_fun[ty1; ty2];
      ty1, ty2. ty_all[ty1; ty2];
      ty, e. lam[ty; e];
      e1, e2. apply[e1; e2];
      ty, e. ty_lam[ty; e];
      e, ty. ty_apply[e; ty]}
   <-->
   ty_top
>>

interactive_rw dest_fsub_exp_fun {| reduce |} :
   'd in nat -->
   bdepth{'ty1} = 'd in nat -->
   bdepth{'ty2} = 'd in nat -->
   'ty1 in FSubCore -->
   'ty2 in FSubCore -->
<:xrewrite<
   dest_exp{fsub type[d] { ty1 -> ty2 };
      x. base[x];
      ty_top;
      ty1, ty2. ty_fun[ty1; ty2];
      ty1, ty2. ty_all[ty1; ty2];
      ty, e. lam[ty; e];
      e1, e2. apply[e1; e2];
      ty, e. ty_lam[ty; e];
      e, ty. ty_apply[e; ty]}
   <-->
   ty_fun[ty1; ty2]
>>

interactive_rw dest_fsub_exp_ty_all {| reduce |} :
   'd in nat -->
   bdepth{'ty1} = 'd in nat -->
   bdepth{'ty2[dummy]} = 'd in nat -->
   'ty1 in FSubCore -->
   bind{x. 'ty2['x]} in FSubCore -->
<:xrewrite<
   dest_exp{fsub type[d] { all x <: ty1. ty2[x] };
      x. base[x];
      ty_top;
      ty1, ty2. ty_fun[ty1; ty2];
      ty1, ty2. ty_all[ty1; ty2];
      ty, e. lam[ty; e];
      e1, e2. apply[e1; e2];
      ty, e. ty_lam[ty; e];
      e, ty. ty_apply[e; ty]}
   <-->
   ty_all[ty1; bind{x. ty2[x]}]
>>

interactive_rw dest_fsub_exp_apply {| reduce |} :
   'd in nat -->
   bdepth{'e1} = 'd in nat -->
   bdepth{'e2} = 'd in nat -->
   'e1 in FSubCore -->
   'e2 in FSubCore -->
<:xrewrite<
   dest_exp{fsub[d] { e1 e2 };
      x. base[x];
      ty_top;
      ty1, ty2. ty_fun[ty1; ty2];
      ty1, ty2. ty_all[ty1; ty2];
      ty, e. lam[ty; e];
      e1, e2. apply[e1; e2];
      ty, e. ty_lam[ty; e];
      e, ty. ty_apply[e; ty]}
   <-->
   apply[e1; e2]
>>

interactive_rw dest_fsub_exp_lambda {| reduce |} :
   'd in nat -->
   bdepth{'ty} = 'd in nat -->
   bdepth{'e[dummy]} = 'd in nat -->
   'ty in FSubCore -->
   bind{x. 'e['x]} in FSubCore -->
<:xrewrite<
   dest_exp{fsub[d] { fun x : ty -> e[x] };
      x. base[x];
      ty_top;
      ty1, ty2. ty_fun[ty1; ty2];
      ty1, ty2. ty_all[ty1; ty2];
      ty, e. lam[ty; e];
      e1, e2. apply[e1; e2];
      ty, e. ty_lam[ty; e];
      e, ty. ty_apply[e; ty]}
   <-->
   lam[ty; bind{x. e[x]}]
>>

interactive_rw dest_fsub_exp_ty_apply {| reduce |} :
   'd in nat -->
   bdepth{'e} = 'd in nat -->
   bdepth{'ty} = 'd in nat -->
   'e in FSubCore -->
   'ty in FSubCore -->
<:xrewrite<
   dest_exp{fsub[d] { e{ty} };
      x. base[x];
      ty_top;
      ty1, ty2. ty_fun[ty1; ty2];
      ty1, ty2. ty_all[ty1; ty2];
      ty, e. lam[ty; e];
      e1, e2. apply[e1; e2];
      ty, e. ty_lam[ty; e];
      e, ty. ty_apply[e; ty]}
   <-->
   ty_apply[e; ty]
>>

interactive_rw dest_fsub_exp_ty_lambda {| reduce |} :
   'd in nat -->
   bdepth{'ty} = 'd in nat -->
   bdepth{'e[dummy]} = 'd in nat -->
   'ty in FSubCore -->
   bind{x. 'e['x]} in FSubCore -->
<:xrewrite<
   dest_exp{fsub[d] { Fun x <: ty -> e[x] };
      x. base[x];
      ty_top;
      ty1, ty2. ty_fun[ty1; ty2];
      ty1, ty2. ty_all[ty1; ty2];
      ty, e. lam[ty; e];
      e1, e2. apply[e1; e2];
      ty, e. ty_lam[ty; e];
      e, ty. ty_apply[e; ty]}
   <-->
   ty_lam[ty; bind{x. e[x]}]
>>

interactive dest_fsub_wf {| intro [] |} : <:xrule<
   <H> >- e IN FSubCore{} -->
   <H>; x: Var{} >- base[x] Type -->
   <H> >- ty_top Type -->
   <H>; ty1: FSubCore{}; ty2: FSubCore{}; bdepth{ty1} = bdepth{ty2} in nat{} >- ty_fun[ty1; ty2] Type -->
   <H>; ty1: FSubCore{}; ty2: FSubCore{}; bdepth{ty2} = bdepth{ty1} +@ 1 in nat{} >- ty_all[ty1; ty2] Type -->
   <H>; ty: FSubCore{}; e: FSubCore{}; bdepth{e} = bdepth{ty} +@ 1 in nat{} >- lam[ty; e] Type -->
   <H>; e1: FSubCore{}; e2: FSubCore{}; bdepth{e1} = bdepth{e2} in nat{} >- apply[e1; e2] Type -->
   <H>; ty: FSubCore{}; e: FSubCore{}; bdepth{e} = bdepth{ty} +@ 1 in nat{} >- ty_lam[ty; e] Type -->
   <H>; e: FSubCore{}; ty: FSubCore{}; bdepth{e} = bdepth{ty} in nat{} >- ty_apply[e; ty] Type -->
   <H> >- dest_exp{e;
      x. base[x];
      ty_top;
      ty1, ty2. ty_fun[ty1; ty2];
      ty1, ty2. ty_all[ty1; ty2];
      ty, e. lam[ty; e];
      e1, e2. apply[e1; e2];
      ty, e. ty_lam[ty; e];
      e, ty. ty_apply[e; ty]} Type
>>

(************************************************************************
 * Separate the language into types and expressions.
 *)
interactive_rw reduce_dest_bterm_mk_bterm {| reduce |} :
   'depth in nat -->
   'op in Operator -->
   'subs in list{FSubCore} -->
   compatible_shapes{'depth; shape{'op}; 'subs} -->
   dest_bterm{mk_bterm{'depth; 'op; 'subs};
      l, r. 'var_case['l; 'r];
      depth, op, subs. 'op_case['depth; 'op; 'subs] }
   <-->
   'op_case['depth; 'op; 'subs]

define unfold_isVar : isVar{'e} <--> <:xterm<
   dest_bterm e with
      l, r -> "true"
    | d, o, s -> "false"
>>

let fold_isVar = makeFoldC << isVar{'e} >> unfold_isVar

interactive isVar_wf : <:xrule<
   <H> >- e IN FSubCore{} -->
   <H> >- isVar{e} Type
>>

define unfold_isTyExp : isTyExp{'e} <--> <:xterm<
   (fix is_ty e ->
      dest_bterm e with
         l, r -> "true"
       | d, o, s ->
            ((o = $TyTop{} in Operator{}
              || o = $TyFun{t1; t2} in Operator{}
              || o = $TyAll{t1; x. t2[x]} in Operator{})
             && all_list{s; x. is_ty x})) e
>>

let fold_isTyExp = makeFoldC << isTyExp{'e} >> unfold_isTyExp

interactive isTyExp_wf : <:xrule<
   <H> >- e IN FSubCore{} -->
   <H> >- isTyExp{e} Type
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
