doc <:doc<
   @begin[doc]
   @spelling{AST compilable}
   @module[M_ir_ast]

   @docoff
   Convert AST to IR.
   We name all intermediate computations.
   @end[doc]
  
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
   @doc{@parents}
>>

extends Base_meta
extends M_util
extends M_ast
extends M_ir

doc <<docoff>>

open Refiner.Refiner.Term
open Term_match_table

open Tactic_type.Sequent
open Tactic_type.Rewrite
open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_meta
open M_util

doc <<"doc"{terms}>>

declare IR{'e}
declare IR{'e1; v. 'e2['v]}
declare IR{'args; 'f; v. 'e['v]}
declare IR_size{'tuple; 'init}

doc <<docoff>>

dform ir_df1 : IR{'e} =
   keyword["IR["] slot{'e} `"]"

dform ir_df2 : IR{'e1; v. 'e2} =
   keyword["IR "] slot{'v} `" = " slot{'e1} keyword[" in"] hspace slot{'e2}

dform ir_df3 : IR{'args; 'f; v. 'e2} =
   keyword["IR "] slot{'v} `" = " slot{'f} `"(" slot{'args} `")" keyword[" in"] hspace slot{'e2}

dform ir_df4 : IR_size{'tuple; 'init} =
   keyword["SIZE_OF["] slot{'tuple} `", " slot{'init} `"]"

(************************************************************************
 * REDUCTION RESOURCE                                                   *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @resources

   @bf{The @Comment!resource[ir_resource]}

   The @tt[ir] resource provides a generic method for
   naming intermediate values.  The @conv[irC] conversion
   can be used to apply this evaluator.

   The implementation of the @tt[ir_resource] and the @tt[irC]
   conversion rely on tables to store the shape of redices, together with the
   conversions for the reduction.

   @end[doc]
   @docoff
>>
let resource ir =
   table_resource_info identity extract_data

let process_ir_resource_rw_annotation = redex_and_conv_of_rw_annotation "ir"

doc <:doc<
   @begin[doc]
   Convert AST operators.
   @end[doc]
>>
prim_rw ir_add_op {| ir |} : IR{AstAddOp} <--> AddOp
prim_rw ir_sub_op {| ir |} : IR{AstSubOp} <--> SubOp
prim_rw ir_mul_op {| ir |} : IR{AstMulOp} <--> MulOp
prim_rw ir_div_op {| ir |} : IR{AstDivOp} <--> DivOp

prim_rw ir_le_op {| ir |} :  IR{AstLeOp}  <--> LeOp
prim_rw ir_lt_op {| ir |} :  IR{AstLtOp}  <--> LtOp
prim_rw ir_ge_op {| ir |} :  IR{AstGeOp}  <--> GeOp
prim_rw ir_gt_op {| ir |} :  IR{AstGtOp}  <--> GtOp
prim_rw ir_eq_op {| ir |} :  IR{AstEqOp}  <--> EqOp
prim_rw ir_neq_op {| ir |} : IR{AstNeqOp} <--> NeqOp

doc <:doc<
   @begin[doc]
   Translating simple expressions.
   @end[doc]
>>
prim_rw ir_num {| ir |} :
   IR{IntExpr[i:n]; v. 'e['v]} <--> 'e[AtomInt[i:n]]

prim_rw ir_bool1 {| ir |} :
   IR{TrueExpr; v. 'e['v]} <--> 'e[AtomTrue]

prim_rw ir_bool2 {| ir |} :
   IR{FalseExpr; v. 'e['v]} <--> 'e[AtomFalse]

prim_rw ir_var {| ir |} :
   IR{VarExpr{'v}; v2. 'e['v2]} <--> 'e[AtomVar{'v}]

doc <:doc<
   @begin[doc]
   Translating simple operations.
   @end[doc]
>>
prim_rw ir_binop {| ir |} :
   IR{BinopExpr{'op; 'e1; 'e2}; v. 'e['v]}
   <-->
   IR{'e1; v1. IR{'e2; v2. 'e[AtomBinop{IR{'op}; 'v1; 'v2}]}}

prim_rw ir_relop {| ir |} :
   IR{RelopExpr{'op; 'e1; 'e2}; v. 'e['v]}
   <-->
   IR{'e1; v1. IR{'e2; v2. 'e[AtomRelop{IR{'op}; 'v1; 'v2}]}}

doc <:doc<
   @begin[doc]
   Translating a function in a let definition.
   @end[doc]
>>
prim_rw ir_fun_lambda {| ir |} :
   IR{FunLambdaExpr{v1. 'body['v1]}; v2. 'e['v2]}
   <-->
   AtomFun{v1. IR{'body['v1]; v2. 'e['v2]}}

doc <:doc<
   @begin[doc]
   Translating an unnamed function.
   @end[doc]
>>
prim_rw ir_lambda {| ir |} :
   IR{LambdaExpr{v1. 'body['v1]}; v2. 'e['v2]}
   <-->
   LetRec{R. Fields{
      FunDef{Label["g":t]; AtomFun{v1. IR{'body['v1]; v3.
         Return{'v3}}}; (**)
      EndDef}};
   R. LetFun{'R; Label["g":t]; g. 'e[AtomVar{'g}]}}

doc <:doc<
   @begin[doc]
   Translating an if expression.
   @end[doc]
>>
prim_rw ir_if {| ir |} :
   IR{IfExpr{'e1; 'e2; 'e3}; v. 'e['v]}
   <-->
   LetRec{R. Fields{
      FunDef{Label["g":t]; AtomFun{v. 'e[AtomVar{'v}]}; (* ? *)
      EndDef}};
   R. LetFun{'R; Label["g":t]; g.
      IR{'e1; v1.
         If{'v1;
            IR{'e2; v2. TailCall{AtomVar{'g}; ArgCons{'v2; ArgNil}}};
            IR{'e3; v3. TailCall{AtomVar{'g}; ArgCons{'v3; ArgNil}}}}}}}

doc <:doc<
   @begin[doc]
   Translating recursive functions.
   @end[doc]
>>
prim_rw ir_let_rec {| ir |} :
   IR{AstLetRec{R. 'bodies['R]; R. 'e1['R]}; v. 'e2['v]}
   <-->
   LetRec{R. IR{'bodies['R]}; R. IR{'e1['R]; v. 'e2['v]}}

prim_rw ir_fields {| ir |} :
   IR{AstFields{'fields}} <--> Fields{IR{'fields}}

prim_rw ir_label {| ir |} :
   IR{AstLabel[t:t]} <--> Label[t:t]

prim_rw ir_fun_def {| ir |} :
   IR{AstFunDef{'label; 'e; 'rest}}
   <-->
   FunDef{IR{'label}; IR{'e; v. Return{'v}}; IR{'rest}} (**)

prim_rw ir_end_def {| ir |} :
   IR{AstEndDef} <--> EndDef

prim_rw ir_let_fun {| ir |} :
   IR{AstLetFun{'R; 'label; f. 'e['f]}; v. 'cont['v]}
   <-->
   LetFun{'R; IR{'label}; f. IR{'e['f]; v. 'cont['v]}}

doc <:doc<
   @begin[doc]
   Translating a let variable definition.
   @end[doc]
>>
prim_rw ir_let_var {| ir |} :
   IR{LetVarExpr{'e1; v. 'e2['v]}; v2. 'e3['v2]}
   <-->
   IR{'e1; v1.
   LetAtom{'v1; v.
   IR{'e2['v]; v2. 'e3['v2]}}}

doc <:doc<
   @begin[doc]
   Translating a function application.
   @end[doc]
>>
prim_rw ir_apply {| ir |} :
   IR{ApplyExpr{'fe; 'args}; v. 'e['v]}
   <-->
   IR{'fe; f.
   IR{'args; 'f; v. 'e['v]}}

doc <:doc<
   @begin[doc]
   Translating a list of arguments.
   @end[doc]
>>
prim_rw ir_arg_cons {| ir |} :
   IR{AstArgCons{'hd; 'tl}; 'f; v. 'e['v]}
   <-->
   IR{'hd; v1.
   LetApply{'f; 'v1; v2.
   IR{'tl; AtomVar{'v2}; v. 'e['v]}}}

prim_rw ir_arg_nil {| ir |} :
   IR{AstArgNil; 'f; v. 'e['v]}
   <-->
   'e['f]

doc <:doc<
   @begin[doc]
   Tuples.
   We use Base_meta arithmetic to figure out the size of a tuple.
   @end[doc]
>>
declare succ{'e}

prim_rw ir_alloc_tuple_cons {| ir |} :
   IR{AstAllocTupleCons{'e; 'rest}; v. 'e2['v]}
   <-->
   IR{'e; v1.
   IR{'rest; v2.
   'e2[AllocTupleCons{'v1; 'v2}]}}

prim_rw ir_alloc_tuple_nil {| ir |} :
   IR{AstAllocTupleNil; v. 'e['v]}
   <-->
   'e[AllocTupleNil]

prim_rw ir_tuple {| ir |} :
   IR{TupleExpr{'tuple}; v. 'e['v]}
   <-->
   IR{'tuple; v.
   LetTuple{IR_size{'tuple; meta_num[0:n]}; 'v; v2. 'e[AtomVar{'v2}]}}

(* Tuple size computations *)
prim_rw ir_size1 {| ir |} :
   IR_size{AstAllocTupleCons{'e; 'rest}; 'count}
   <-->
   IR_size{'rest; succ{'count}}

prim_rw ir_size2 {| ir |} :
   IR_size{'AstAllotTupleNil; meta_num[n:n]}
   <-->
   Length[n:n]

prim_rw reduce_succ {| ir |} :
   succ{meta_num[n:n]}
   <-->
   meta_sum[n:n, 1:n]

let resource ir +=
   [ <<meta_sum[i1:n, i2:n]>>, reduce_meta_sum]

doc <:doc<
   @begin[doc]
   Subscripting.
   @end[doc]
>>
prim_rw ir_subscript_expr {| ir |} :
   IR{SubscriptExpr{'e1; 'e2}; v. 'e['v]}
   <-->
   IR{'e1; v1.
   IR{'e2; v2.
   LetSubscript{'v1; 'v2; v. 'e[AtomVar{'v}]}}}

doc <:doc<
   @begin[doc]
   Assignments.
   They are *always* followed by an expression.
   @end[doc]
>>
prim_rw ir_assign_expr {| ir |} :
   IR{AssignExpr{'e1; 'e2; 'e3; 'e4}; v. 'e['v]}
   <-->
   IR{'e1; v1.
   IR{'e2; v2.
   IR{'e3; v3.
   SetSubscript{'v1; 'v2; 'v3; IR{'e4; v. 'e['v]}}}}}

doc <:doc<
   @begin[doc]
   Some optimizations.
   @end[doc]
>>
prim_rw opt_let_var {| ir |} :
   LetAtom{AtomVar{'v1}; v2. 'e['v2]}
   <-->
   'e['v1]

(* *)

doc <:doc<
   @begin[doc]
   A program is compilable if it can be converted to an atom
   that is the return value of the program.
   @end[doc]
>>
prim prog_ir :
    sequent { <H> >- compilable{IR{'e; v. Return{'v}}} } -->
    sequent { <H> >- compilable{AST{'e}} } = it

(*
 * Top-level conversion and tactic.
 *)
let irTopC_env e =
   get_resource_arg (env_arg e) get_ir_resource

let irTopC = funC irTopC_env

let irC =
   repeatC (sweepDnC irTopC)

let irT =
   prog_ir thenT rw irC 0

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
