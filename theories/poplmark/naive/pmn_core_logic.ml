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
define unfold_ProofStep : ProofStep <--> ProofStep{Sequent}

(*
 * Type well-formedness.
 *)
define unfold_ty_top_wf : ty_top_wf <--> <:xquoterule<
   fsub{| <H> >- top <: top |}
>>

define unfold_ty_fun_wf : ty_fun_wf <--> <:xquoterule<
   fsub{| <H> >- ty1 <: top |} -->
   fsub{| <H> >- ty2 <: top |} -->
   fsub{| <H> >- ty1 -> ty2 <: top |}
>>

define unfold_ty_all_wf : ty_all_wf <--> <:xquoterule<
   fsub{| <H> >- ty1 <: top |} -->
   fsub{| <H>; X <: top >- ty2[X] <: top |} -->
   fsub{| <H> >- all X <: ty1. ty2[X] <: top |}
>>

(*
 * Subtyping rules.
 *)
define unfold_sa_tvar : sa_tvar <--> <:xquoterule<
   fsub{| <H>; X: T; <J[X]> >- X <: X |}
>>

define unfold_sa_trans_tvar : sa_trans_tvar <--> <:xquoterule<
   fsub{| <H>; X: U; <J[X]> >- U <: T |} -->
   fsub{| <H>; X: U; <J[X]> >- X <: T |}
>>

define unfold_sa_arrow : sa_arrow <--> <:xquoterule<
   fsub{| <H> >- T1 <: S1 |} -->
   fsub{| <H> >- S2 <: T2 |} -->
   fsub{| <H> >- S1 -> S2 <: T1 -> T2 |}
>>

define unfold_sa_all : sa_all <--> <:xquoterule<
   fsub{| <H> >- T1 <: S1 |} -->
   fsub{| <H>; X: T1 >- S2[X] <: T2[X] |} -->
   fsub{| <H> >- all X <: S1. S2[X] <: all X <: T1. T2[X] |}
>>

(*
 * Expression typing rules.
 *)
define unfold_t_var : t_var <--> <:xquoterule<
   fsub{| <H>; x: T; <J[x]> >- x : T |}
>>

define unfold_t_abs : t_abs <--> <:xquoterule<
   fsub{| <H> >- T1 <: top |} -->
   fsub{| <H>; x: T1 >- e[x] : T2 |} -->
   fsub{| <H> >- fun x : T1 -> e[x] : T1 -> T2 |}
>>

define unfold_t_app : t_app <--> <:xquoterule<
   fsub{| <H> >- e1 : T11 -> T12 |} -->
   fsub{| <H> >- e2 : T11 |} -->
   fsub{| <H> >- e1 e2 : T12 |}
>>

define unfold_t_tabs : t_tabs <--> <:xquoterule<
   fsub{| <H> >- T1 <: top |} -->
   fsub{| <H>; X: T1 >- t2 : T2 |} -->
   fsub{| <H> >- Fun X <: T1 -> e[X] : all X <: T1. T2[X] |}
>>

define unfold_t_tapp : t_tapp <--> <:xquoterule<
   fsub{| <H> >- e : all X <: T11. T12[X] |} -->
   fsub{| <H> >- T2 <: T11  |}-->
   fsub{| <H> >- e{T2} : T12[T2] |}
>>

define unfold_t_sub : t_sub <--> <:xquoterule<
   fsub{| <H> >- e : S |} -->
   fsub{| <H> >- S <: T |} -->
   fsub{| <H> >- e : T |}
>>

(*
 * Define the logic.
 *)
define unfold_fsub_logic : FSubLogic <--> <:xterm<
   ["ty_top_wf"; "ty_fun_wf"; "ty_all_wf";
    "sa_tvar"; "sa_trans_tvar"; "sa_arrow"; "sa_all";
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
