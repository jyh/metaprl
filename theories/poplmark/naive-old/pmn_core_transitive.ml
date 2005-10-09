(*
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
extends Pmn_core_final
extends Pmn_core_type
extends Pmn_core_subtype

(*
 * Lemmas.
 *)
interactive fsub_ref : <:itt_rule<
    <H> >- T IN TyExp -->
    <H> >- T <: T
>>

(*
 * Transitivity for Fsub typing.
 *)
interactive fsub_trans 'T2 : <:itt_rule<
    <H> >- T2 IN TyExp -->
    <H> >- T1 IN TyExp -->
    <H> >- T3 IN TyExp -->
    <H> >- T1 <: T2 -->
    <H> >- T2 <: T3 -->
    <H> >- T1 <: T3
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
