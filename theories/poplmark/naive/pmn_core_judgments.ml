(*
 * The judgments for FSub.
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
extends Itt_hoas_sequent_native
extends Pmn_core_terms

open Lm_printf

open Simple_print
open Basic_tactics

(*
 * Judgments include subtyping.
 *)
define unfold_dest_judgment :
   dest_judgment{'e;
      x. 'base['x];
      t1, t2. 'sub['t1; 't2];
      'other}
   <-->
<:xterm<
   dest_bterm e with
      l, r ->
         base[var{l; r}]
    | d, o, s ->
         if is_same_op{o; $"subtype"{t1; t2}} then
            sub[nth{s; 0}; nth{s; 1}]
         else
            other
>>

interactive dest_judgment_type {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "BTerm" -->
   "wf" : <H>; x: "Var" >- base[x] Type -->
   "wf" : <H>; t1: "BTerm"; t2: "BTerm" >- subtype[t1; t2] Type -->
   "wf" : <H> >- other Type -->
   <H> >- dest_judgment{e; x. base[x]; t1, t2. subtype[t1; t2]; other} Type
>>

(*
 * Define the language of judgments.
 *)
define unfold_is_judgment : isJudgment{'e} <--> <:xterm<
   dest_judgment{e;
      x. "true";
      t1, t2. isTyExp{t1} && isTyExp{t2};
      "false"}
>>

interactive is_judgment_type {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "BTerm" -->
   <H> >- isJudgment{e} Type
>>

(*
 * Define the rules.
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
 *)

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
