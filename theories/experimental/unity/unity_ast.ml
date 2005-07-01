doc <:doc<
   @begin[spelling]
   @end[spelling]

   @module[UNITY]
   This module defines a UNITY abstract syntax.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2003 Adam Granicz, Caltech

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Adam Granicz
   @email{granicz@cs.caltech.edu}
   @end[license]
>>
extends Base_theory

doc <:doc<
   @terms
   Binary operators.
>>
declare AddOp
declare SubOp
declare MulOp
declare DivOp

declare LtOp
declare LeOp
declare EqOp
declare NeqOp
declare GeOp
declare GtOp

doc <:doc<
   Types.
>>
declare TyInt{'pos}
declare TyArray{'array; 'size; 'pos}

doc <:doc<
   @modsubsection{Expressions}
>>
declare TrueExp{'pos}
declare FalseExp{'pos}
declare VarExp{'v; 'pos}
declare IntExp[i:n]{'pos}
declare BinopExp{'op; 'e1; 'e2; 'pos}
declare SubscriptExp{'e1; 'e2; 'pos}
declare ApplyExp{'f; 'args; 'pos}

doc <:doc<
   @modsubsection{Statements}
   We have simple, conditional and quantified assignment statements.
>>
declare Body{'inits; 'assigns}

declare Declare{'ty; 'pos; v. 'rest['v]}
declare Identity{'e1; 'e2; 'pos; 'rest}

doc <:doc<
   Simple assignment statements assign a list of values to
   a list of lvalues.
>>
declare Statement{'lvalues; 'values; 'pos; 'next}

doc <:doc<
   Conditional assignment statements assign a list of values to
   a list of lvalues when a given condition holds.
>>
declare Statement{'lvalues; 'values; 'cond; 'pos; 'next}

doc <:doc<
   Quantified assignment statements assign a list of values to
   a list of lvalues over a range when a given condition holds.
>>
declare Statement{'range; 'cond; 'pos; 'assign; 'next}

doc <:doc<
    We need a skip (leave state unchanged).
>>
declare StatementSkip

doc <:doc<
   Programs.
>>
declare Program[name:s]{'program; 'pos}

doc <:doc<
   Dummy position term.
>>
declare DummyPos

doc <:doc<
   Generic list terms.
>>
declare UCons{'el; 'list}
declare UNil

doc <:doc<
   Sequent tag.
>>
declare unity

doc docoff

(************************************************************************
 * Display forms
 *)

(*
 * Precedences.
 *)
prec prec_subscript
prec prec_bool
prec prec_add
prec prec_mul
prec prec_apply

prec prec_subscript < prec_bool
prec prec_bool < prec_add
prec prec_add < prec_mul
prec prec_mul < prec_apply

(*
 * Types.
 *)
dform ty_int_df : TyInt{'pos} =
   `"integer"

dform ty_array_df : TyArray{'array; 'size; 'pos} =
   bf["array"] `"[" slot{'size} `"]" bf[" of "] slot{'array}

(*
 * Expressions.
 *)
dform true_exp_df : TrueExp{'pos} =
   bf["true"]

dform false_exp_df : FalseExp{'pos} =
   bf["false"]

dform var_exp_df : VarExp{'v; 'pos} =
   slot{'v}

dform int_exp_df : IntExp[i:n]{'pos} =
   slot[i:n]

dform binop_exp_df1 : parens :: "prec"[prec_add] :: BinopExp{AddOp; 'e1; 'e2; 'pos} =
   slot["lt"]{'e1} `"+" slot["le"]{'e2}

dform binop_exp_df2 : parens :: "prec"[prec_add] :: BinopExp{SubOp; 'e1; 'e2; 'pos} =
   slot["lt"]{'e1} `"-" slot["le"]{'e2}

dform binop_exp_df3 : parens :: "prec"[prec_mul] :: BinopExp{MulOp; 'e1; 'e2; 'pos} =
   slot["lt"]{'e1} `"*" slot["le"]{'e2}

dform binop_exp_df4 : parens :: "prec"[prec_add] :: BinopExp{DivOp; 'e1; 'e2; 'pos} =
   slot["lt"]{'e1} `"/" slot["le"]{'e2}


dform binop_exp_df5 : parens :: "prec"[prec_bool] :: BinopExp{LtOp; 'e1; 'e2; 'pos} =
   slot["lt"]{'e1} `"<" slot["le"]{'e2}

dform binop_exp_df6 : parens :: "prec"[prec_bool] :: BinopExp{LeOp; 'e1; 'e2; 'pos} =
   slot["lt"]{'e1} Nuprl_font!le slot["le"]{'e2}

dform binop_exp_df7 : parens :: "prec"[prec_bool] :: BinopExp{GtOp; 'e1; 'e2; 'pos} =
   slot["lt"]{'e1} `">" slot["le"]{'e2}

dform binop_exp_df8 : parens :: "prec"[prec_bool] :: BinopExp{GeOp; 'e1; 'e2; 'pos} =
   slot["lt"]{'e1} Nuprl_font!ge slot["le"]{'e2}

dform binop_exp_df9 : parens :: "prec"[prec_bool] :: BinopExp{EqOp; 'e1; 'e2; 'pos} =
   slot["lt"]{'e1} `"=" slot["le"]{'e2}

dform binop_exp_df10 : parens :: "prec"[prec_bool] :: BinopExp{NeqOp; 'e1; 'e2; 'pos} =
   slot["lt"]{'e1} Nuprl_font!neq slot["le"]{'e2}


dform subscript_exp_df : SubscriptExp{'e1; 'e2; 'pos} =
   slot{'e1} `"[" slot{'e2} `"]"

dform apply_exp_df : "prec"[prec_apply] :: ApplyExp{'f; 'args; 'pos} =
   slot{'f} `"(" slot{'args} `")"

(*
 * Lists.
 *)
dform u_nil_df : UNil = `""

dform u_cons_df1 : UCons{'arg; UNil} =
   slot{'arg}

dform u_cons_df2 : UCons{'arg; 'rest} =
   slot{'arg} `", " slot{'rest}

(*
 * Temporary terms.
 *)
declare PROGRAM{'t}
declare DECL{'t}
declare IDENTITY{'t}
declare BODY{'t}

(*
 * Programs.
 *)
dform prog_df : Program[name:s]{'program; 'pos} =
   pushm[0] hzone bf["program"] `" " slot[name:s] hspace
   PROGRAM{'program}
   pushm[0] szone bf["end"] ezone popm ezone popm

dform prog_df1 : PROGRAM{Declare{'ty; 'pos; v. 'prog['v]}} =
   pushm[0] szone bf["declare"] ezone popm hspace slot{DECL{Declare{'ty; 'pos; v. 'prog['v]}}}

dform prog_df2 : PROGRAM{Identity{'e1; 'e2; 'pos; 'prog}} =
   pushm[0] szone bf["always"] ezone popm hspace slot{IDENTITY{Identity{'e1; 'e2; 'pos; 'prog}}}

dform prog_df3 : PROGRAM{Body{'inits; 'assigns}} =
   pushm[0] szone bf["initially"] ezone popm hspace slot{BODY{'inits}}
   pushm[0] szone bf["assign"] ezone popm hspace slot{BODY{'assigns}}

dform prog_df4 : DECL{Declare{'ty; 'pos; v. 'prog['v]}} =
   pushm[3] szone slot{'v} `": " slot{'ty} ezone popm hspace DECL{'prog['v]}

dform prog_df5 : DECL{'a} =
   PROGRAM{'a}

dform prog_df6 : IDENTITY{Identity{'e1; 'e2; 'pos; 'prog}} =
   pushm[3] szone slot{'e1} `" = " slot{'e2} ezone popm hspace IDENTITY{'prog}

dform prog_df7 : IDENTITY{'a} =
   PROGRAM{'a}

dform prog_df_8 : BODY{Statement{'lvalues; 'values; 'pos; 'next}} =
   pushm[3] szone slot{'lvalues} `" = " slot{'values} ezone popm hspace slot{BODY{'next}}

dform prog_df_8 : BODY{Statement{'lvalues; 'values; 'cond; 'pos; 'next}} =
   pushm[3] szone slot{'lvalues} `" = " slot{'values} bf[" if "] slot{'cond} ezone popm hspace slot{BODY{'next}}

dform prog_df6 : BODY{StatementSkip} = bf["skip"]

(*
 * Sequent tag.
 *)
dform unity_df : unity = bf["unity"]

