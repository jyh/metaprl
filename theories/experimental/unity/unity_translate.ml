doc <:doc<
   @begin[spelling]
   @end[spelling]

   @module[UNITY]
   This module defines the translation between UNITY and
   an abstract source language.

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

extends Unity_ast
extends Unity_source

doc <:doc<
   @terms
   Translation operators and helper terms.
>>
declare Alias{'e}
declare Alias_args{'args}
declare Lv{'e}
declare Syncronize{'vars; 'xxxx}

doc <:doc<
   @rewrites
   Translation rewrites.
   First, we define the alias operator on each expression.
>>

prim_rw alias_int :
   Alias{IntExp[i:n]{'pos}} <--> IntExp[i:n]{'pos}

prim_rw alias_true :
   Alias{TrueExp{'pos}} <--> TrueExp{'pos}

prim_rw alias_false :
   Alias{FalseExp{'pos}} <--> FalseExp{'pos}

prim_rw alias_var :
   Alias{VarExp{'var_v; 'pos}} <--> VarExp{'var_v; 'pos}

prim_rw alias_binop :
   Alias{BinopExp{'op; 'e1; 'e2; 'pos}}
   <-->
   BinopExp{'op; Alias{'e1}; Alias{'e2}; 'pos}

prim_rw alias_subscript :
   Alias{SubscriptExp{'e1; 'e2; 'pos}}
   <-->
   SubscriptExp{Alias{'e1}; Alias{'e2}; 'pos}

prim_rw alias_apply :
   Alias{ApplyExp{'f; 'args; 'pos}}
   <-->
   ApplyExp{Lv{'f}; Alias_args{'args}; 'pos}

doc <:doc<
   Translating a list of arguments.
>>

prim_rw alias_args1 :
   Alias_args{UCons{'e; 'rest}} <--> UCons{Alias{'e}; Alias_args{'rest}}

prim_rw alias_args2 :
   Alias_args{UNil} <--> UNil

doc <:doc<
   Second, we define the left-value operator on each expression.
>>

prim_rw lv_int :
   Lv{IntExp[i:n]{'pos}} <--> IntExp[i:n]{'pos}

prim_rw lv_true :
   Lv{TrueExp{'pos}} <--> TrueExp{'pos}

prim_rw lv_false :
   Lv{FalseExp{'pos}} <--> FalseExp{'pos}

prim_rw lv_var :
   Lv{VarExp{'var_v; 'pos}} <--> VarExp{'var_v; 'pos}

prim_rw lv_binop :
   Lv{BinopExp{'op; 'e1; 'e2; 'pos}}
   <-->
   BinopExp{'op; Lv{'e1}; Lv{'e2}; 'pos}

prim_rw lv_subscript :
   Lv{SubscriptExp{'e1; 'e2; 'pos}}
   <-->
   SubscriptExp{Lv{'e1}; Alias{'e2}; 'pos}

prim_rw lv_apply :
   Lv{ApplyExp{'f; 'args; 'pos}}
   <-->
   ApplyExp{Lv{'f}; Alias_args{'args}; 'pos}

doc <:doc<
   The syncronization operator.
>>

prim_rw sync_vars :
   Syncronize{UCons{VarExp{'var_v; 'pos}; 'rest}; 'var_changed}
   <-->
   Source_if{BinopExp{NeqOp; Lv{VarExp{'var_v; 'pos}}; Alias{VarExp{'var_v; 'pos}}; 'pos};
             Source_set{VarExp{'var_changed; 'pos}; TrueExp{'pos};
                        Source_set{Alias{VarExp{'var_v; 'pos}}; Lv{VarExp{'var_v; 'pos}}; StatementSkip}};
             StatementSkip;
             Syncronize{'rest; 'var_changed}}

(************************************************************************
 * Display forms
 *)

