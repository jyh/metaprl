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

open Itt_rfun
open Itt_logic

(************************************************************************
 * The reflected language.
 *)
define unfold_fsub_core : FSubCore <--> <:xterm<
   Lang [$TyTop{};
         $TyFun{ty1; ty2};
         $TyAll{ty1; x. ty2};
         $Lambda{ty; x. e};
         $Apply{e1; e2};
         $TyLambda{ty; x. e};
         $TyApply{e; ty}]
>>

let fold_fsub_core = makeFoldC << FSubCore >> unfold_fsub_core

(************************************************************************
 * Display forms.
 *)
dform top_df : <:xterm< fsub type [d] { top } >> =
   `"Top[" slot{'d} `"]"

dform ty_fun_df : parens :: "prec"[prec_fun] :: <:xterm< fsub type [d] { ty1 -> ty2 } >> =
   szone pushm[3] slot{'ty1} `" ->[" slot{'d} `"]" hspace slot{'ty2} popm ezone

dform ty_all_df : parens :: "prec"[prec_quant] :: <:xterm< fsub type [d] { all x <: ty1. ty2 } >> =
   szone pushm[3] `"all[" slot{'d} `" " slot{'x} `" <: " slot{'ty1} `"." hspace slot{'ty2} popm ezone

dform lambda_df : parens :: "prec"[prec_lambda] :: <:xterm< fsub [d] { fun x : ty -> e } >> =
   szone pushm[3] `"fun[" slot{'d} `" " slot{'x} `" : " slot{'ty} `" ->" hspace slot{'e} popm ezone

dform apply_df : parens :: "prec"[prec_apply] :: <:xterm< fsub [d] { e1 e2 } >> =
   szone pushm[3] slot{'e1} `" @[" slot{'d} `"]" hspace slot{'e2} popm ezone

dform ty_lambda_df : parens :: "prec"[prec_lambda] :: <:xterm< fsub [d] { Fun x <: ty -> e } >> =
   szone pushm[3] `"Fun[" slot{'d} `" " slot{'x} `" <: " slot{'ty} `" ->" hspace slot{'e} popm ezone

dform ty_apply_df : parens :: "prec"[prec_apply] :: <:xterm< fsub [d] { e{ty} } >> =
   szone pushm[3] slot{'e} `"@[" slot{'d} `"]{" slot{'ty} `"}" popm ezone

(************************************************************************
 * Basic well-formedness.
 *)
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

interactive ty_all_wf : <:xrule<
   <H> >- "bdepth"{ty1} = d in "nat" -->
   <H> >- "bdepth"{ty2["dummy"]} = d in "nat" -->
   <H> >- ty1 IN "FSubCore" -->
   <H> >- "bind"{x. ty2[x]} IN "FSubCore" -->
   <H> >- fsub type [d] { all x <: ty1. ty2[x] } IN "FSubCore"
>>

interactive lambda_wf : <:xrule<
   <H> >- "bdepth"{ty} = d in "nat" -->
   <H> >- "bdepth"{e["dummy"]} = d in "nat" -->
   <H> >- ty IN "FSubCore" -->
   <H> >- "bind"{x. e[x]} IN "FSubCore" -->
   <H> >- fsub [d] { fun x : ty -> e[x] } IN "FSubCore"
>>

interactive apply_wf : <:xrule<
   <H> >- "bdepth"{e1} = d in "nat" -->
   <H> >- "bdepth"{e2} = d in "nat" -->
   <H> >- e1 IN "FSubCore" -->
   <H> >- e2 IN "FSubCore" -->
   <H> >- fsub [d] { e1 e2 } IN "FSubCore"
>>

interactive ty_lambda_wf : <:xrule<
   <H> >- "bdepth"{ty} = d in "nat" -->
   <H> >- "bdepth"{e["dummy"]} = d in "nat" -->
   <H> >- ty IN "FSubCore" -->
   <H> >- "bind"{x. e[x]} IN "FSubCore" -->
   <H> >- fsub [d] { Fun x <: ty -> e[x] } IN "FSubCore"
>>

interactive ty_apply_wf : <:xrule<
   <H> >- "bdepth"{e1} = d in "nat" -->
   <H> >- "bdepth"{e2} = d in "nat" -->
   <H> >- e1 IN "FSubCore" -->
   <H> >- e2 IN "FSubCore" -->
   <H> >- fsub [d] { e1{e2} } IN "FSubCore"
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
