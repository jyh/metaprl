(*x
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
extends Itt_hoas_theory

open Itt_equal
open Itt_dfun
open Itt_logic

(************************************************************************
 * Define the reflected logic.x
 *)

(*
 * Type expressions.
 *)
reflected_logic Types =
struct
   (* Type expressions *)
   declare typeclass TyExp -> Term

   declare TyTop : TyExp
(*
   declare TyFun{'ty1 : TyExp; 'ty2 : TyExp} : TyExp
   declare TyAll{'ty1 : TyExp; x : TyExp. 'ty2 : TyExp} : TyExp
 *)
end;;

(*
   (* Expressions *)
   declare typeclass Exp -> Term

   declare Apply{'e1 : Exp; 'e2 : Exp} : Exp
   declare Lambda{'ty : TyExp; x : Exp. 'e : Exp} : Exp
   declare TyApply{'e : Exp; 'ty : TyExp} : Exp
   declare TyLambda{'ty : TyExp; x : TyExp. 'e : Exp} : Exp

   (* Judgments *)
   declare typeclass Prop -> Term

   declare fsub_subtype{'ty1 : TyExp; 'ty2 : TyExp} : Prop
   declare fsub_member{'e : Exp; 'ty : TyExp} : Prop

   (* Sequents *)
   declare typeclass Judgment -> Perv!Judgment

   declare typeclass Hyp -> Ty

   declare typeclass TyVal : Hyp -> Term
   declare typeclass TyPower : Hyp -> Term

   declare TyVal{'ty : TyExp} : TyVal
   declare TyPower{'ty : TyExp} : TyPower

   (* Sequents have dependent types *)
   declare type TyElem{'a : Ty} : Ty

   declare rewrite TyElem{TyVal} <--> Exp
   declare rewrite TyElem{TyPower} <--> TyExp

   declare sequent [fsub] { exst a: Hyp. TyElem{'a} : 'a >- Prop } : Judgment
*)

(************************************************************************
 * Display forms.
 *)
dform ty_exp_df : <:xterm< $`"TyExp" >> =
   `"TyExp"

dform exp_df : <:xterm< $`"Exp" >> =
   `"Exp"

dform top_df : <:xterm< $`"TyTop" >> =
   `"Top"

dform ty_fun_df : parens :: "prec"[prec_fun] :: <:xterm< xquote{d; fsub { ty1 -> ty2 }} >> =
   szone pushm[3] slot{'ty1} `" ->[" slot{'d} `"]" hspace slot{'ty2} popm ezone

dform ty_all_df : parens :: "prec"[prec_quant] :: <:xterm< xquote{d; fsub { all x <: ty1. ty2 }} >> =
   szone pushm[3] `"all[" slot{'d} `"] " slot{'x} `" <: " slot{'ty1} `"." hspace slot{'ty2} popm ezone

dform lambda_df : parens :: "prec"[prec_lambda] :: <:xterm< xquote{d; fsub { fun x : ty -> e }} >> =
   szone pushm[3] `"fun[" slot{'d} `"] " slot{'x} `" : " slot{'ty} `" ->" hspace slot{'e} popm ezone

dform apply_df : parens :: "prec"[prec_apply] :: <:xterm< xquote{d; fsub { e1 e2 }} >> =
   szone pushm[3] slot{'e1} `" @[" slot{'d} `"]" hspace slot{'e2} popm ezone

dform ty_lambda_df : parens :: "prec"[prec_lambda] :: <:xterm< xquote{d; fsub { Fun x <: ty -> e }} >> =
   szone pushm[3] `"Fun[" slot{'d} `"] " slot{'x} `" <: " slot{'ty} `" ->" hspace slot{'e} popm ezone

dform ty_apply_df : parens :: "prec"[prec_apply] :: <:xterm< xquote{d; fsub { e{ty} }} >> =
   szone pushm[3] slot{'e} `"@[" slot{'d} `"]{" slot{'ty} `"}" popm ezone

dform ty_power_df : <:xterm< xquote{d; "TyPower"} >> =
   `"Power"

dform ty_val_df : <:xterm< xquote{d; "TyVal"} >> =
   `"Val"

dform ty_power_df : <:xterm< xquote{d; TyPower{ty}} >> =
   `"Power(" slot{'ty} `")"

dform ty_power_df : <:xterm< xquote{d; TyVal{ty}} >> =
   `"Val(" slot{'ty} `")"

dform fsub_df : <:xterm< xquote{d; "fsub"} >> =
   `"fsub"

dform fsub_subtype_df : parens :: "prec"[prec_equal] :: <:xterm< xquote{d; fsub_subtype{t1; t2}} >> =
   szone pushm[3] slot{'t1} `" <:[" slot{'d} `"]" hspace slot{'t2} popm ezone

dform fsub_member_df : parens :: "prec"[prec_apply] :: <:xterm< xquote{d; fsub_member{e; ty}} >> =
   szone pushm[3] slot{'e} `" " Mpsymbols!member `"[" slot{'d} `"]" hspace slot{'ty} popm ezone

dform fsub_Judgment_df : <:xterm< xquote{d; "Judgment"} >> =
   `"Judgment[" slot{'d} `"]"

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
