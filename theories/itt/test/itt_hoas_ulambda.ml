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

declare Apply{'e1; 'e2}
declare Lambda{x. 'e['x]}

(*
 * The language.
 *)
define unfold_ulambda : ULambda <--> <:xterm<
   Lang [#"Apply"{x; x}; #"Lambda"{\x. x}]
>>

let fold_ulambda   = makeFoldC << ULambda >> unfold_ulambda

interactive ulambda_type : <:xrule<
   <H> >- "ULambda" Type
>>

interactive var_wf : <:xrule<
   <H> >- v IN "Var" -->
   <H> >- v IN "ULambda"
>>

interactive apply_wf {| intro [] |} : <:xrule<
   <H> >- e1 IN "ULambda" -->
   <H> >- e2 IN "ULambda" -->
   <H> >- depth IN "nat" -->
   <H> >- "bdepth"{e1} = depth in "int" -->
   <H> >- "bdepth"{e2} = depth in "int" -->
   <H> >- ($`[depth] "Apply"{e1; e2}) IN "ULambda"
>>

interactive ulambda_elim1 'H : <:xrule<
   <H>; e: "ULambda"; <J[e]>; l: "nat"; r: "nat" >- P["var"{l; r}] -->
   <H>; e: "ULambda"; <J[e]>; depth: "nat"; e1: "ULambda"; e2: "ULambda"; P[e1]; P[e2] >- P["mk_bterm"{depth; #(f x); [e1; e2]}] -->
   <H>; e: "ULambda"; <J[e]>; depth: "nat"; e1: "ULambda"; P[e1] >- P["mk_bterm"{depth; #(fun x -> y); [e1]}] -->
   <H>; e: "ULambda"; <J[e]> >- P[e]
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
