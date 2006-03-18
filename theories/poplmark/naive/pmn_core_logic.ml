(*
 * Logical rules for core Fsub.
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
extends Pmn_core_terms
extends Pmn_core_judgments

(*
 * Subtyping rules.
 *)
prim sa_top : <:xrule<
   fsub{| <H> >- fsub_subtype{'T; TyTop} |}
>>

prim sa_tvar 'H : <:xrule<
   fsub{| <H>; X: TyPower{T}; <J[X]> >- fsub_subtype{X; X} |}
>>

prim sa_trans_tvar 'H : <:xrule<
   fsub{| <H>; X: TyPower{U}; <J[X]> >- fsub_subtype{U; T} |} -->
   fsub{| <H>; X: TyPower{U}; <J[X]> >- fsub_subtype{X; T} |}
>>

prim sa_arrow : <:xrule<
   fsub{| <H> >- fsub_subtype{T1; S1} |} -->
   fsub{| <H> >- fsub_subtype{S2; T2} |} -->
   fsub{| <H> >- fsub_subtype{TyFun{S1; S2}; TyFun{T1; T2}} |}
>>

prim sa_all : <:xrule<
   fsub{| <H> >- fsub_subtype{T1; S1} |} -->
   fsub{| <H>; X: TyPower{T1} >- fsub_subtype{S2[X]; T2[X]} |} -->
   fsub{| <H> >- fsub_subtype{TyAll{S1; X. S2[X]}; TyAll{T1; X. T2[X]}} |}
>>

(*
 * Expression typing rules.
 *)
prim t_var 'H : <:xrule<
   fsub{| <H>; x: T; <J[x]> >- fsub_member{x; T} |}
>>

prim t_abs : <:xrule<
   fsub{| <H>; x: T1 >- fsub_member{e[x]; T2} |} -->
   fsub{| <H> >- fsub_member{Lambda{T1; x. e[x]}; TyFun{T1; T2}} |}
>>

prim t_app TyArg{'T11} : <:xrule<
   fsub{| <H> >- fsub_member{e1; TyFun{T11; T12}} |} -->
   fsub{| <H> >- fsub_member{e2; T11} |} -->
   fsub{| <H> >- fsub_member{Apply{e1; e2}; T12} |}
>>

prim t_tabs : <:xrule<
   fsub{| <H>; X: TyPower{T1} >- fsub_member{e[X]; T2[X]} |} -->
   fsub{| <H> >- fsub_member{TyLambda{T1; X. e[X]}; TyAll{T1; X. T2[X]}} |}
>>

prim t_tapp TyArg{'T11} bind{x. 'T12['x]} : <:xrule<
   fsub{| <H> >- fsub_member{e; TyAll{T11; X. T12[X]}} |} -->
   fsub{| <H> >- fsub_subtype{T2; T11}  |}-->
   fsub{| <H> >- fsub_member{TyApply{e; T2}; T12[T2]} |}
>>

prim t_sub TyArg{'S} : <:xrule<
   fsub{| <H> >- fsub_member{e; S} |} -->
   fsub{| <H> >- fsub_subtype{S; T} |} -->
   fsub{| <H> >- fsub_member{e; T} |}
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
