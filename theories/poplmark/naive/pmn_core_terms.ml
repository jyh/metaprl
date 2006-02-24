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
extends Base_theory

open Basic_tactics
open Itt_equal
open Itt_dfun
open Itt_logic

(************************************************************************
 * Display forms.
 *)

(*
 * Closed terms.
 *)
dform ty_exp_df : TyExp =
   `"TyExp"

dform exp_df : Exp =
   `"Exp"

dform top_df : TyTop =
   `"Top"

dform ty_fun_df : parens :: "prec"[prec_fun] :: <:xterm< TyFun{ty1; ty2} >> =
   szone pushm[3] slot{'ty1} `" ->" hspace slot{'ty2} popm ezone

dform ty_all_df : parens :: "prec"[prec_quant] :: <:xterm< TyAll{ty1; x. ty2} >> =
   szone pushm[3] `"all " slot{'x} `" <: " slot{'ty1} `"." hspace slot{'ty2} popm ezone

dform lambda_df : parens :: "prec"[prec_lambda] :: <:xterm< Lambda{ty; x. e} >> =
   szone pushm[3] `"fun " slot{'x} `" : " slot{'ty} `" ->" hspace slot{'e} popm ezone

dform apply_df : parens :: "prec"[prec_apply] :: <:xterm< Apply{e1; e2} >> =
   szone pushm[3] slot{'e1} hspace slot{'e2} popm ezone

dform ty_lambda_df : parens :: "prec"[prec_lambda] :: <:xterm< TyLambda{ty; x. e} >> =
   szone pushm[3] `"Fun " slot{'x} `" <: " slot{'ty} `" ->" hspace slot{'e} popm ezone

dform ty_apply_df : parens :: "prec"[prec_apply] :: <:xterm< TyApply{e; ty} >> =
   szone pushm[3] slot{'e} `"@{" slot{'ty} `"}" popm ezone

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
