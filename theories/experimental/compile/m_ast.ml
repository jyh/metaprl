doc <:doc<
   @spelling{IR AST}
   @begin[doc]
   @module[M_ast]
   This file defines the terms needed to represent the M AST.
   @end[doc]

   @begin[verbatim]
   e ::= i                          (numbers)
      |  b                          (Booleans)
      |  v                          (variables)
      |  fun x -> e                 (functions)
      |  (e1, e2)                   (pairs)
      |  e1 binop e2                (binary operations)
      |  e1 relop e2                (relational operations)
      |  e1[e2]                     (subscripting)
      |  e1[e2] <- e3               (assignments)
      |  e1(e2, ...)                (function calls)
      |  if e1 then e2 else e3      (conditionals)
      |  let v = e1 in e2           (let-var)
      |  let f(v1, ...) = e1 in e2  (let-fun)
      |  let rec f1(v1, ...) = e1   (let-fun-rec)
             and f2(u1, ...) = e2
         ...
         in e3
   @end[verbatim]
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

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Summary
doc <:doc< @docoff >>

doc <:doc<
   @begin[doc]
   Operators.
   @end[doc]
>>
declare AstAddOp
declare AstSubOp
declare AstMulOp
declare AstDivOp

declare AstLeOp
declare AstLtOp
declare AstGeOp
declare AstGtOp
declare AstEqOp
declare AstNeqOp

doc <:doc<
   @begin[doc]
   Expressions
   @end[doc]
>>
declare TrueExpr
declare FalseExpr
declare IntExpr[i:n]
declare BinopExpr{'op; 'e1; 'e2}
declare RelopExpr{'op; 'e1; 'e2}
declare VarExpr{'v}
declare LambdaExpr{v. 'e['v]}
declare FunLambdaExpr{v. 'e['v]}

declare IfExpr{'e1; 'e2; 'e3}
declare SubscriptExpr{'e1; 'e2}
declare AssignExpr{'e1; 'e2; 'e3; 'e4}
declare ApplyExpr{'f; 'args}
declare LetVarExpr{'e1; v. 'e2['v]}

doc <:doc<
   @begin[doc]
   Arguments.
   @end[doc]
>>
declare AstArgNil
declare AstArgCons{'head; 'tail}

doc <:doc<
   @begin[doc]
   Mutually recursive functions.
   We need post-parsing rewrite rules (relaxed mode) to create these.
   @end[doc]
>>
declare AstLetRec{R1. 'e1['R1]; R2. 'e2['R2]}
declare AstFields{'fields}
declare AstLabel[label:t]
declare AstFunDef{'label; 'e; 'cont}
declare AstEndDef
declare AstLetFun{'R; 'label; f. 'cont['f]}

doc <:doc<
   @begin[doc]
   Tuples.
   @end[doc]
>>
declare AstAllocTupleNil
declare AstAllocTupleCons{'e; 'rest}
declare TupleExpr{'tuple}

doc <:doc<
   @begin[doc]
   The parsed program is represented as an AST term.
   @end[doc]
>>
declare AST{'e}

(************************************************************************
 * Display forms
 *)

(* Precedences *)
prec prec_seq
prec prec_comma
prec prec_if
prec prec_let
prec prec_rel
prec prec_add
prec prec_mul
prec prec_fun
prec prec_assign
prec prec_subscript

prec prec_seq < prec_comma
prec prec_comma < prec_if
prec prec_if < prec_let
prec prec_let < prec_rel
prec prec_rel < prec_add
prec prec_add < prec_mul
prec prec_mul < prec_fun
prec prec_fun < prec_assign
prec prec_assign < prec_subscript

(* Integers *)
dform int_expr_df : IntExpr[n:n] =
   `"#" slot[n:n]

(* Booleans *)
dform true_expr_df : TrueExpr =
   bf["true"]

dform false_expr_df : FalseExpr =
   bf["false"]

(* Variables *)
dform var_expr_df : VarExpr{'v} =
   Nuprl_font!downarrow slot{'v}

(* Binary operations *)
dform add_binop_expr_df : parens :: "prec"[prec_add] :: BinopExpr{AstAddOp; 'e1; 'e2} =
   slot["lt"]{'e1} `" + " slot["le"]{'e2}

dform sub_binop_expr_df : parens :: "prec"[prec_add] :: BinopExpr{AstSubOp; 'e1; 'e2} =
   slot["lt"]{'e1} `" - " slot["le"]{'e2}

dform mul_binop_expr_df : parens :: "prec"[prec_mul] :: BinopExpr{AstMulOp; 'e1; 'e2} =
   slot["lt"]{'e1} `" * " slot["le"]{'e2}

dform div_binop_expr_df : parens :: "prec"[prec_mul] :: BinopExpr{AstDivOp; 'e1; 'e2} =
   slot["lt"]{'e1} `" / " slot["le"]{'e2}

(* Relational operations *)
dform lt_relop_expr_df : parens :: "prec"[prec_rel] :: RelopExpr{AstLtOp; 'e1; 'e2} =
   slot["lt"]{'e1} `" < " slot["le"]{'e2}

dform le_binop_expr_df : parens :: "prec"[prec_rel] :: RelopExpr{AstLeOp; 'e1; 'e2} =
   slot["lt"]{'e1} `" " Nuprl_font!le `" " slot["le"]{'e2}

dform gt_relop_expr_df : parens :: "prec"[prec_rel] :: RelopExpr{AstGtOp; 'e1; 'e2} =
   slot["lt"]{'e1} `" > " slot["le"]{'e2}

dform ge_binop_expr_df : parens :: "prec"[prec_rel] :: RelopExpr{AstGeOp; 'e1; 'e2} =
   slot["lt"]{'e1} `" " Nuprl_font!ge `" " slot["le"]{'e2}

dform eq_relop_expr_df : parens :: "prec"[prec_rel] :: RelopExpr{AstEqOp; 'e1; 'e2} =
   slot["lt"]{'e1} `" = " slot["le"]{'e2}

dform neq_binop_expr_df : parens :: "prec"[prec_rel] :: RelopExpr{AstNeqOp; 'e1; 'e2} =
   slot["lt"]{'e1} `" " Nuprl_font!neq `" " slot["le"]{'e2}

(* (Unnamed) functions *)
dform lambda_expr_df : parens :: "prec"[prec_fun] :: LambdaExpr{v. 'e} =
   szone pushm[3] Nuprl_font!lambda slot{'v} `"." hspace slot{'e} popm ezone

dform fun_lambda_expr_df : parens :: "prec"[prec_fun] :: FunLambdaExpr{v. 'e} =
   szone pushm[3] Nuprl_font!lambda `"*" slot{'v} `"." hspace slot{'e} popm ezone

(* if expressions *)
dform if_expr_df1 : parens :: "prec"[prec_if] :: except_mode[tex] :: IfExpr{'e1; 'e2; 'e3} =
   szone pushm[0] pushm[3] bf["if "] slot{'e1} bf[" then"] hspace
   slot{'e2} popm hspace
   pushm[3] bf[" else"] hspace slot{'e3} popm popm ezone

dform if_expr_df2 : parens :: "prec"[prec_if] :: mode[tex] :: IfExpr{'e1; 'e2; 'e3} =
   bf["if "] slot{'e1} bf[" then "] slot{'e2} bf[" else "] slot{'e3}

(* Subscript expressions *)
dform subscript_expr_df : parens :: "prec"[prec_subscript] :: SubscriptExpr{'e1; 'e2} =
   slot{'e1} `"[" slot{'e2} `"]"

(* Assignments *)
dform assign_expr_df : parens :: "prec"[prec_assign] :: AssignExpr{'e1; 'e2; 'e3; 'e4} =
   slot{'e1} `"[" slot{'e2} `"] <- " slot{'e3} `";" slot{'e4}

(* Function application *)
dform apply_expr_df : ApplyExpr{'e; 'args} =
   slot{'e} `"(" slot{'args} `")"

(* Let-var *)
dform let_var_expr_df : parens :: "prec"[prec_let] :: LetVarExpr{'e1; v. 'e2} =
   szone pushm[3] bf["let "] slot{'v} `" = " slot{'e1} bf[" in"] hspace slot["lt"]{'e2} popm ezone

(* Recursive functions *)
dform ast_let_rec_df : parens :: "prec"[prec_let] :: AstLetRec{R1. 'e1; R2. 'e2} =
   szone pushm[3] bf["let "] bf["rec "] slot{'R1} `"." hspace 'e1 popm ezone hspace slot{'R2} `"."
   bf[" in"] hspace slot["lt"]{'e2}

dform ast_fields_df : parens :: "prec"[prec_let] :: AstFields{'fields} =
   szone pushm[0] pushm[2] bf["{ "] slot["lt"]{'fields} popm hspace bf["}"] popm ezone

dform ast_fun_def_df : parens :: "prec"[prec_let] :: AstFunDef{'label; 'e; 'rest} =
   szone pushm[3] bf["fun "] slot{'label} `" =" hspace slot{'e} popm ezone hspace 'rest

dform ast_end_def_df : AstEndDef =
   `""

dform ast_label_df : AstLabel[s:t] =
   `"\"" slot[s:t] `"\""

dform ast_let_fun_df : parens :: "prec"[prec_let] :: AstLetFun{'R; 'label; f. 'e} =
   szone pushm[3] bf["let"] bf[" fun "] slot{'f} `" = " slot{'R} `"." slot{'label} `" " bf[" in"]
   hspace slot["lt"]{'e} popm ezone

(* Arguments *)
dform ast_arg_cons_df1 : parens :: "prec"[prec_comma] :: AstArgCons{'a1; AstArgCons{'a2; 'rest}} =
   slot{'a1} `", " slot["lt"]{AstArgCons{'a2; 'rest}}

dform ast_arg_cons_df2 : parens :: "prec"[prec_comma] :: AstArgCons{'a; AstArgNil} =
   slot{'a}

dform ast_arg_cons_df2 : parens :: "prec"[prec_comma] :: AstArgCons{'a; 'b} =
   slot{'a} `" :: " slot{'b}

dform ast_arg_nil_df : parens :: "prec"[prec_comma] :: AstArgNil =
   `""

(* Tuples *)
dform ast_alloc_tuple_nil_df : parens :: "prec"[prec_comma] :: AstAllocTupleNil =
   `""

dform ast_alloc_tuple_cons_df1 : parens :: "prec"[prec_comma] :: AstAllocTupleCons{'e; 'rest} =
   slot{'e} `", " slot["lt"]{'rest}

dform ast_alloc_tuple_cons_df2 : parens :: "prec"[prec_comma] :: AstAllocTupleCons{'e; AstAllocTupleNil} =
   slot{'e}

dform tuple_expr_df : parens :: "prec"[prec_comma] :: TupleExpr{'tuple} =
   `"(" slot{'tuple} `")"

(* AST term *)
dform ast_df : AST{'e} =
   bf["AST term="] slot{'e}
