(*
 * Typed AST.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003-2005 Mojave Group, Caltech
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
extends Itt_theory
extends Itt_hoas_lang2

open Basic_tactics

(************************************************************************
 * The reflected language.
 *)
define unfold_fsub_core : FSubCore <--> <:xterm<
   Lang [#"TyTop";
         #"TyFun"{ty1; ty2};
         #"TyAll"{ty1; \x. ty2};
         #"Lambda"{ty; \x. e};
         #"Apply"{e1; e2};
         #"TyLambda"{ty; \x. e};
         #"TyApply"{e; ty}]
>>

let fold_fsub_core = makeFoldC << FSubCore >> unfold_fsub_core

interactive fsub_core_wf : <:xrule<
   <H> >- "FSubCore" Type
>>

interactive top_wf : <:xrule<
   <H> >- d IN "nat" -->
   <H> >- fsub type [d] { top } IN "FSubCore"
>>

interactive ty_fun_wf : <:xrule<
   <H> >- "bdepth"{ty1} = d in "nat" -->
   <H> >- "bdepth"{ty2} = d in "nat" -->
   <H> >- ty1 IN "FSubCore" -->
   <H> >- ty2 IN "FSubCore" -->
   <H> >- fsub type [d] { ty1 -> ty2 } IN "FSubCore"
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
