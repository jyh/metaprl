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
extends Itt_hoas_sequent_native

open Basic_tactics

(*
 * Proof steps are over sequents.
 *)
define unfold_ProofRule : ProofRule <--> ProofRule{Sequent}
define unfold_ProofStep : ProofStep <--> ProofStep{Sequent}
define unfold_Provable  : Provable{'t} <--> Provable{Sequent; it; 't}

reflected_logic fsub_core =
struct
   (*
    * Type well-formedness.
    *)
   interactive top_wf : <:xrule<
      fsub{| <H> >- top <: top |}
   >>

   interactive ty_fun_wf : <:xrule<
      fsub{| <H> >- ty1 <: top |} -->
      fsub{| <H> >- ty2 <: top |} -->
      fsub{| <H> >- ty1 -> ty2 <: top |}
   >>

   interactive ty_all_wf : <:xrule<
      fsub{| <H> >- ty1 <: top |} -->
      fsub{| <H>; X <: top >- ty2[X] <: top |} -->
      fsub{| <H> >- all X <: ty1. ty2[X] <: top |}
   >>

   (*
    * Subtyping rules.
    *)
   interactive sa_tvar 'H : <:xrule<
      fsub{| <H>; X: T; <J[X]> >- X <: X |}
   >>

   interactive sa_trans_tvar 'H : <:xrule<
      fsub{| <H>; X: U; <J[X]> >- U <: T |} -->
      fsub{| <H>; X: U; <J[X]> >- X <: T |}
   >>

   interactive sa_arrow : <:xrule<
      fsub{| <H> >- T1 <: S1 |} -->
      fsub{| <H> >- S2 <: T2 |} -->
      fsub{| <H> >- S1 -> S2 <: T1 -> T2 |}
   >>

   interactive sa_all : <:xrule<
      fsub{| <H> >- T1 <: S1 |} -->
      fsub{| <H>; X: T1 >- S2[X] <: T2[X] |} -->
      fsub{| <H> >- all X <: S1. S2[X] <: all X <: T1. T2[X] |}
   >>

   (*
    * Expression typing rules.
    *)
   interactive t_var 'H : <:xrule<
      fsub{| <H>; x: T; <J[x]> >- x : T |}
   >>

   interactive t_abs : <:xrule<
      fsub{| <H> >- T1 <: top |} -->
      fsub{| <H>; x: T1 >- e[x] : T2 |} -->
      fsub{| <H> >- fun x : T1 -> e[x] : T1 -> T2 |}
   >>

(*
   interactive t_app 'T11 : <:xrule<
      fsub{| <H> >- e1 : T11 -> T12 |} -->
      fsub{| <H> >- e2 : T11 |} -->
      fsub{| <H> >- e1 e2 : T12 |}
   >>

   interactive t_tabs : <:xrule<
      fsub{| <H> >- T1 <: top |} -->
      fsub{| <H>; X: T1 >- e[X] : T2[X] |} -->
      fsub{| <H> >- Fun X <: T1 -> e[X] : all X <: T1. T2[X] |}
   >>

   interactive t_tapp 'T11 bind{x. 'T12['x]} : <:xrule<
      fsub{| <H> >- e : all X <: T11. T12[X] |} -->
      fsub{| <H> >- T2 <: T11  |}-->
      fsub{| <H> >- e{T2} : T12[T2] |}
   >>

   interactive t_sub 'S : <:xrule<
      fsub{| <H> >- e : S |} -->
      fsub{| <H> >- S <: T |} -->
      fsub{| <H> >- e : T |}
   >>
*)
end

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
