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
extends Itt_hoas_lang2

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

interactive lambda_wf {| intro [] |} : <:xrule<
   <H> >- "bind"{\x. e[x]} IN "ULambda" -->
   <H> >- depth IN "nat" -->
   <H> >- "bdepth"{e["dummy"]} = depth in "int" -->
   <H> >- ($`[depth] "Lambda"{\x. e[x]}) IN "ULambda"
>>

interactive ulambda_elim 'H : <:xrule<
   <H>; <J>; v: "Var" >- P[v] -->
   <H>; <J>; e1: "ULambda"; e2: "ULambda"; P[e1]; P[e2];
      "bdepth"{e1} = "bdepth"{e2} in "int" >- P[$`["bdepth"{e1}] "Apply"{e1; e2}] -->
   <H>; <J>; e: "ULambda"; P[e] >- P[$`["bdepth"{e}] "Lambda"{\x. $,"subst"{e; x}}] -->
   <H>; e: "ULambda"; <J> >- P[e]
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
