(*
 * This file defines the terms needed to represent the M AST.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Adam Granicz, Caltech
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
 * Author: Adam Granicz @email{granicz@cs.caltech.edu}
 * @end[license]
 *)

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>
extends M_util
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
declare AssignExpr{'e1; 'e2; 'e3}
(*declare SeqExpr{'e1; 'e2}*)
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
