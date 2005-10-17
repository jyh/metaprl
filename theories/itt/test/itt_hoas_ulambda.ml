(*
 * Untyped lambda calculus.
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
extends Itt_hoas_lang

open Basic_tactics

(*
 * The language.
 *)
define unfold_ulambda : ULambda <--> <:itt<
   Lang ([#(fun x -> e); #(f x)])
>>

define unfold_lambda : Lambda{'depth; 'e} <--> <:itt<
   mk_bterm{depth; #(fun x -> y); [e]}
>>

define unfold_apply : Apply{'depth; 'e1; 'e2} <--> <:itt<
   mk_bterm{depth; #(f x); [e1; e2]}
>>

let fold_ulambda = makeFoldC << ULambda >> unfold_ulambda
let fold_lambda  = makeFoldC << Lambda{'depth; 'e} >> unfold_lambda
let fold_apply   = makeFoldC << Apply{'depth; 'e1; 'e2} >> unfold_apply

interactive ulambda_type : <:itt_rule<
   <H> >- << ULambda Type >>
>>

interactive var_wf {| intro [] |} : <:itt_rule<
   <H> >- l IN Nat -->
   <H> >- r IN Nat -->
   <H> >- ~<l; r> IN ULambda
>>

(*
interactive apply_wf {| intro [] |} : <:itt_rule<
   <H> >- depth IN Nat -->
   <H> >- e1 IN "ULambda" -->
   <H> >- e2 IN "ULambda" -->
   <H> >- "Apply"{depth; e1; e2} IN ULambda
>>

interactive lambda_wf {| intro [] |} : <:itt_rule<
   <H> >- depth IN Nat -->
   <H> >- e IN "ULambda" -->
   <H> >- "Lambda"{depth; e} IN "ULambda"
>>
 *)

interactive ulambda_elim1 'H : <:itt_rule<
   <H>; e: ULambda; <J[e]>; l: Nat; r: Nat >- P[~<l; r>] -->
   <H>; e: ULambda; <J[e]>; bdepth: Nat; e1: ULambda; e2: ULambda; P[e1]; P[e2] >- P[mk_bterm{bdepth; #(f x); [e1; e2]}] -->
   <H>; e: ULambda; <J[e]>; bdepth: Nat; e1: ULambda; P[e1] >- P[mk_bterm{bdepth; #(fun x -> y); [e1]}] -->
   <H>; e: ULambda; <J[e]> >- P[e]
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
