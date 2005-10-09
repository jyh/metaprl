(*
 * Subtyping rules.
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
extends Itt_theory

open Basic_tactics

(*
 * Well-formedness.
 *)
interactive fsub_wf {| intro [] |} : <:itt_rule<
    <H> >- S IN TyExp -->
    <H> >- T IN TyExp -->
    <H> >- (S <: T) type
>>

interactive fsub_sa_top {| intro [] |} : <:itt_rule<
    <H> >- S IN TyExp -->
    <H> >- S <: Top
>>

interactive fsub_sa_refl_var {| intro [] |} : <:itt_rule<
    <H> >- T IN TyVar -->
    <H> >- type { ~T } <: type { ~T }
>>

interactive fsub_sa_trans_tvar 'U : <:itt_rule<
    <H> >- type { ~X } <: U -->
    <H> >- U <: T -->
    <H> >- type { ~X } <: T
>>

interactive fsub_sa_arrow {| intro [] |} : <:itt_rule<
    <H> >- T1 <: S1 -->
    <H> >- S2 <: T2 -->
    <H> >- type { S1 -> S2 } <: type { T1 -> T2 }
>>

interactive fsub_sa_all {| intro [] |} : <:itt_rule<
    <H> >- T1 <: S1 -->
    <H>; X: TyVar; type { ~X } <: T1 >- S2[X] <: T2[X] -->
    <H> >- type { all X <: S1. S2[X] } <: type { all X <: T1. T2[X] }
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
