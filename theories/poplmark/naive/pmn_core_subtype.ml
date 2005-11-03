(*
 * Subtyping judgments in Fsub.
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
extends Pmn_core_judgments

open Basic_tactics

(*
 * The subtyping rules.
 *)
define unfold_sa_top : sa_top <--> <:xquoterule<
   <H> >- T <: "TyTop"
>>

define unfold_sa_tvar : sa_tvar <--> <:xquoterule<
   <H>; X: T; <J[X]> >- X <: X
>>

define unfold_sa_trans_tvar : sa_trans_tvar <--> <:xquoterule<
   <H>; X: U; <J[X]> >- U <: T -->
   <H>; X: U; <J[X]> >- X <: T
>>

define unfold_sa_arrow : sa_arrow <--> <:xquoterule<
   <H> >- T1 <: S1 -->
   <H> >- S2 <: T2 -->
   <H> >- TyFun{S1; S2} <: TyFun{T1; T2}
>>

define unfold_sa_all : sa_all <--> <:xquoterule<
   <H> >- T1 <: S1 -->
   <H>; X: T1 >- S2[X] <: T2[X] -->
   <H> >- TyAll{S1; X. S2[X]} <: TyAll{T1; X. T2[X]}
>>

(*
 * Typing rules.
 *)
define unfold_t_var : t_var <--> <:xquoterule<
   <H>; x: T; <J[x]> >- x :in: T
>>

define unfold_t_abs : t_abs <--> <:xquoterule<
   <H>; x: T1 >- e[x] :in: T2 -->
   <H> >- Lambda{T1; x. e[x]} :in: TyFun{T1; T2}
>>

define unfold_t_app : t_app <--> <:xquoterule<
   <H> >- e1 :in: TyFun{T11; T12} -->
   <H> >- e2 :in: T11 -->
   <H> >- Apply{e1; e2} :in: T12
>>

define unfold_t_tabs : t_tabs <--> <:xquoterule<
   <H>; X: T1 >- t2 :in: T2 -->
   <H> >- TyLambda{T1; X. e[X]} :in: TyAll{T1; X. T2[X]}
>>

define unfold_t_tapp : t_tapp <--> <:xquoterule<
   <H> >- e :in: TyAll{T11; X. T12[X]} -->
   <H> >- T2 <: T11 -->
   <H> >- TyApply{e; T2} :in: T12[T2]
>>

define unfold_t_sub : t_sub <--> <:xquoterule<
   <H> >- e :in: S -->
   <H> >- S <: T -->
   <H> >- e :in: T
>>

(*
 * Define the logic.
 *)
define unfold_fsub_logic : FSubLogic <--> <:xterm<
   ["sa_top"; "sa_tvar"; "sa_trans_tvar"; "sa_arrow"; "sa_all";
    "t_var"; "t_abs"; "t_app"; "t_tabs"; "t_tapp"; "t_sub"]
>>

interactive fsub_logic_wf {| intro [] |} : <:xrule<
   <H> >- "FSubLogic" IN Logic{Sequent}
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
