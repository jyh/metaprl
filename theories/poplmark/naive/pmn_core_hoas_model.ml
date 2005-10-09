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

(************************************************************************
 * Type classes.
 *)
define unfold_tenv : TEnv <--> <:itt<
    Prod n: int * ({ 0..n- } -> soas_TyExp)
>>

define unfold_venv : VEnv <--> <:itt<
    Prod n: int * ({ 0..n- } -> soas_Exp)
>>

prim_rw unfold_ty_var_type : <:itt_rw<
    TyVar
    <-->
    int
>>

prim_rw unfold_ty_exp : <:itt_rw<
    TyExp
    <-->
    << TEnv >> -> soas_TyExp
>>

prim_rw unfold_var_type : <:itt_rw<
    Var
    <-->
    int
>>

prim_rw unfold_exp : <:itt_rw<
    Exp
    <-->
    << VEnv >> -> soas_Exp
>>

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
    fun tenv -> tenv v
>>

prim_rw unfold_ty_fun : <:itt_rw<
   type { t1 -> t2 }
   <-->
   fun tenv -> soas_type { itt { t1 tenv } -> itt { t2 tenv } }
>>

prim_rw unfold_ty_all : <:itt_rw<
   type { all X <: t1. t2[X] }
   <-->
   fun tenv -> soas_type { all X <: itt { t1 tenv }. (* t2[fst tenv] (tenv with X) *) t2[X] }
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
