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

open Basic_tactics

doc <:doc<
   Sequents must include only terms from fsub.
>>
define unfold_fsub_Sequent : Sequent <--> <:xterm<
   { s: Itt_hoas_sequent!Sequent | Pmn_core_terms!Provable{$`[0] "meta_type"{| >- meta_member{s; "Judgment"} |}} }
>>

doc docoff

(*
 * Proof steps are over sequents.
 *)
reflected_logic fsub_core =
struct
   (*
    * Subtyping rules.
    *)
   interactive sa_top : <:xrule<
      fsub{| <H> >- T <: top |}
   >>

   interactive sa_tvar 'H : <:xrule<
      fsub{| <H>; X <: T; <J[X]> >- X <: X |}
   >>

   interactive sa_trans_tvar 'H : <:xrule<
      fsub{| <H>; X <: U; <J[X]> >- U <: T |} -->
      fsub{| <H>; X <: U; <J[X]> >- X <: T |}
   >>

   interactive sa_arrow : <:xrule<
      fsub{| <H> >- T1 <: S1 |} -->
      fsub{| <H> >- S2 <: T2 |} -->
      fsub{| <H> >- S1 -> S2 <: T1 -> T2 |}
   >>

   interactive sa_all : <:xrule<
      fsub{| <H> >- T1 <: S1 |} -->
      fsub{| <H>; X <: T1 >- S2[X] <: T2[X] |} -->
      fsub{| <H> >- all X <: S1. S2[X] <: all X <: T1. T2[X] |}
   >>

   (*
    * Expression typing rules.
    *)
   interactive t_var 'H : <:xrule<
      fsub{| <H>; x: T; <J[x]> >- x : T |}
   >>

   interactive t_abs : <:xrule<
      fsub{| <H>; x: T1 >- e[x] : T2 |} -->
      fsub{| <H> >- fun x : T1 -> e[x] : T1 -> T2 |}
   >>

   interactive t_app TyVal{'T11} : <:xrule<
      fsub{| <H> >- e1 : T11 -> T12 |} -->
      fsub{| <H> >- e2 : T11 |} -->
      fsub{| <H> >- e1 e2 : T12 |}
   >>

   interactive t_tabs : <:xrule<
      fsub{| <H>; X <: T1 >- e[X] : T2[X] |} -->
      fsub{| <H> >- Fun X <: T1 -> e[X] : all X <: T1. T2[X] |}
   >>

   interactive t_tapp TyVal{'T11} bind{x. TyVal{'T12['x]}} : <:xrule<
      fsub{| <H> >- e : all X <: T11. T12[X] |} -->
      fsub{| <H> >- T2 <: T11  |}-->
      fsub{| <H> >- e{T2} : T12[T2] |}
   >>

   interactive t_sub TyVal{'S} : <:xrule<
      fsub{| <H> >- e : S |} -->
      fsub{| <H> >- S <: T |} -->
      fsub{| <H> >- e : T |}
   >>
end

(*
 * Display forms.
 *)
dform provable_df : Provable{'e} =
   szone pushm[0] `"<< " slot{'e} hspace `">>" popm ezone

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
