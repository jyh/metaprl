(*
 * Type rules for Fsub.
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
extends Pmn_core_tast
extends Pmn_core_model

open Basic_tactics

(*
 * Well-formedness rules.
 * Necessary because we are using ITT.
 *)
interactive fsub_top_wf {| intro [] |} : <:itt_rule<
    <H> >- top IN TyExp
>>

interactive fsub_var_wf {| intro [] |} : <:itt_rule<
    <H> >- T IN TyVar -->
    <H> >- type { ~T } IN TyExp
>>

interactive fsub_fun_wf {| intro [] |} : <:itt_rule<
    <H> >- t1 IN TyExp -->
    <H> >- t2 IN TyExp -->
    <H> >- type { t1 -> t2 } IN TyExp
>>

interactive fsub_all_wf {| intro [] |} : <:itt_rule<
    <H> >- t1 IN TyExp -->
    <H>; X: TyVar >- t2[X] IN TyExp -->
    <H> >- type { all X <: t1. t2[X] } IN TyExp
>>

interactive fsub_itt_apply_wf {| intro [] |} : <:itt_rule<
    <H> >- f IN TyVar -> TyExp -->
    <H> >- x IN TyVar -->
    <H> >- f x IN TyExp
>>

(*
 * The actual typing rules.
 *)
interactive fsub_abs : <:itt_rule<
    <H>; x: Var; x :: t1 >- e[x] :: t2 -->
    <H> >- exp { fun x: t1 -> e[x] } :: type { t1 -> t2 }
>>

interactive fsub_app 't1 : <:itt_rule<
    <H> >- e1 :: type { t1 -> t2 } -->
    <H> >- e2 :: t1 -->
    <H> >- exp { e1 e2 } :: t2
>>

interactive fsub_tabs : <:itt_rule<
    <H>; X: TyExp; u: X <: t1 >- e[X] :: t2[X] -->
    <H> >- exp { Fun X <: t1 -> e[X] } :: type { all X <: t1. t2[X] }
>>

interactive fsub_tapp <:fsub_type< all X <: t1. t2[X] >> : <:itt_rule<
    <H> >- e :: type { all X <: t1. t2[X] } -->
    <H> >- t <: t1 -->
    <H> >- exp { e{t} } :: t2[t]
>>

interactive fsub_sub 'S : <:itt_rule<
    <H> >- e :: S -->
    <H> >- S <: T -->
    <H> >- e :: T
>>

(*
 * The rules are bidirectional.
 *)
interactive fsub_app_inverse 't1 'H : <:itt_rule<
    <H>; exp { e1 e2 } :: t2; <J> >- e2 :: t1 -->
    <H>; exp { e1 e2 } :: t2; <J>; e1 :: t1 -> t2 >- C -->
    <H>; exp { e1 e2 } :: t2; <J> >- C
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
