(*
 * ITT model for the HOAS.
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
extends Pmn_core_hoas_terms
extends Pmn_core_soas_model

open Basic_tactics

(************************************************************************
 * Type classes.
 *)
define unfold_tenv : TEnv <--> <:itt< sif soas_TyExp >>
define unfold_venv : VEnv <--> <:itt< sif soas_Exp >>

prim_rw unfold_ty_var_type : <:itt_rw<
    TyVar
    <-->
    "int"
>>

prim_rw unfold_ty_exp : <:itt_rw<
    TyExp
    <-->
    << TEnv >> -> soas_TyExp
>>

prim_rw unfold_var_type : <:itt_rw<
    Var
    <-->
    "int"
>>

prim_rw unfold_exp : <:itt_rw<
    Exp
    <-->
    << TEnv * VEnv >> -> soas_Exp
>>

let fold_tenv = makeFoldC << TEnv >> unfold_tenv
let fold_venv = makeFoldC << VEnv >> unfold_venv

(************************************************************************
 * Type expressions.
 *)
prim_rw unfold_ty_top : <:itt_rw<
    top
    <-->
    fun tenv -> soas_top
>>

prim_rw unfold_ty_var : <:itt_rw<
    type { ~v }
    <-->
    fun tenv -> sif { tenv @ v }
>>

prim_rw unfold_ty_fun : <:itt_rw<
   type { t1 -> t2 }
   <-->
   fun tenv -> soas_type { itt { t1 tenv } -> itt { t2 tenv } }
>>

prim_rw unfold_ty_all : <:itt_rw<
   type { all X <: t1. t2[X] }
   <-->
   fun tenv -> soas_type { all X <: itt { t1 tenv }. itt { t2[<< Var{length_ifun{'tenv}} >>] (sif { tenv += X }) } }
>>

(************************************************************************
 * Expressions.
 *)
prim_rw unfold_var : <:itt_rw<
   exp { ~v }
   <-->
   fun env ->
      let tenv, venv = env in
         sif { venv @ v }
>>

prim_rw unfold_apply : <:itt_rw<
   exp { e1 e2 }
   <-->
   fun env -> soas_exp { (itt { e1 env }) (itt { e2 env }) }
>>

prim_rw unfold_lambda : <:itt_rw<
   exp { fun x : ty -> e[x] }
   <-->
   fun env ->
      let tenv, venv = env in
          soas_exp {
             fun x : itt { ty tenv } ->
                itt { e[sif |venv| ] (tenv, sif { venv += x }) }
          }
>>

prim_rw unfold_ty_apply : <:itt_rw<
   exp { e{ty} }
   <-->
   fun env ->
      let tenv, venv = env in
         soas_exp {
            (itt { e env }){ itt { ty tenv } }
         }
>>

prim_rw unfold_ty_lambda : <:itt_rw<
   exp { Fun X <: ty -> e[X] }
   <-->
   fun env ->
      let tenv, venv = env in
         soas_exp {
            Fun X <: (itt { ty tenv }) ->
               itt { e[sif |tenv| ] (sif { tenv += X }, venv) }
         }
>>

(************************************************************************
 * Well-formedness.
 *)
interactive tenv_wf {| intro [] |} : <:itt_rule<
   <H> >- << "type"{TEnv} >>
>>

interactive venv_wf {| intro [] |} : <:itt_rule<
   <H> >- << "type"{VEnv} >>
>>

interactive ty_top_wf {| intro [] |} : <:itt_rule<
    <H> >- top IN TyExp
>>

interactive ty_var_wf {| intro [] |} : <:itt_rule<
    <H> >- v IN TyVar -->
    <H> >- type { ~v } IN TyExp
>>

interactive ty_fun_wf {| intro [] |} : <:itt_rule<
   <H> >- t1 IN TyExp -->
   <H> >- t2 IN TyExp -->
   <H> >- type { t1 -> t2 } IN TyExp
>>

interactive ty_all_wf {| intro [] |} : <:itt_rule<
   <H> >- t1 IN TyExp -->
   <H>; X: TyExp >- t2[X] IN TyExp -->
   <H> >- type { all X <: t1. t2[X] } IN TyExp
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
