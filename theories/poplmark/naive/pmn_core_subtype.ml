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

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
