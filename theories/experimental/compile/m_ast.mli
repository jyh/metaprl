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
   @parents
>>
extends Summary
doc docoff

doc <:doc<
   Operators.
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
   Expressions
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
   Arguments.
>>
declare AstArgNil
declare AstArgCons{'head; 'tail}

doc <:doc<
   Mutually recursive functions.
   We need post-parsing rewrite rules (relaxed mode) to create these.
>>
declare AstLetRec{R1. 'e1['R1]; R2. 'e2['R2]}
declare AstFields{'fields}
declare AstLabel[label:s]
declare AstFunDef{'label; 'e; 'cont}
declare AstEndDef
declare AstLetFun{'R; 'label; f. 'cont['f]}

doc <:doc<
   Tuples.
>>
declare AstAllocTupleNil
declare AstAllocTupleCons{'e; 'rest}
declare TupleExpr{'tuple}

doc <:doc<
   The parsed program is represented as an AST term.
>>
declare AST{'e}

doc <:doc<
   Input grammar for the input syntax.
>>

declare m : Lexer

declare tok_eof : Terminal

declare tok_id[v:s] : Terminal
declare tok_num[n:n] : Terminal

declare tok_and : Terminal
declare tok_else : Terminal
declare tok_end : Terminal
declare tok_false : Terminal
declare tok_fun : Terminal
declare tok_if : Terminal
declare tok_in : Terminal
declare tok_let : Terminal
declare tok_then : Terminal
declare tok_true : Terminal
declare tok_rec : Terminal

declare tok_arrow : Terminal
declare tok_assign : Terminal
declare tok_comma : Terminal
declare tok_div : Terminal
declare tok_dot : Terminal
declare tok_eq : Terminal
declare tok_ge : Terminal
declare tok_gt : Terminal
declare tok_lbrack : Terminal
declare tok_le : Terminal
declare tok_lparen : Terminal
declare tok_lt : Terminal
declare tok_minus : Terminal
declare tok_neq : Terminal
declare tok_rem : Terminal
declare tok_plus : Terminal
declare tok_rbrack : Terminal
declare tok_rparen : Terminal
declare tok_semi : Terminal
declare tok_times : Terminal

lex_token m : "[[:space:]]+" (* Ignored *)
lex_token m : "[(][*]" "[*][)]" (* Comments *)

lex_token m : "\'" --> tok_eof

lex_token m : "[_a-zA-Z][_a-zA-Z0-9]*" --> tok_id[lexeme:s]
lex_token m: "[0-9]+" --> tok_num[lexeme:n]

lex_token m : "and" --> tok_and
lex_token m : "else" --> tok_else
lex_token m : "end" --> tok_end
lex_token m : "false" --> tok_false
lex_token m : "fun" --> tok_fun
lex_token m : "if" --> tok_if
lex_token m : "in" --> tok_in
lex_token m : "let" --> tok_let
lex_token m : "then" --> tok_then
lex_token m : "true" --> tok_true
lex_token m : "rec" --> tok_rec

lex_token m : "->" --> tok_arrow
lex_token m : "<-" --> tok_assign
lex_token m : "," --> tok_comma
lex_token m : "/" --> tok_div
lex_token m : "\." --> tok_dot
lex_token m : "=" --> tok_eq
lex_token m : ">=" --> tok_ge
lex_token m : ">" --> tok_gt
lex_token m : "\[" --> tok_lbrack
lex_token m : "<=" --> tok_le
lex_token m : "[(]" --> tok_lparen
lex_token m : "<" --> tok_lt
lex_token m : "-" --> tok_minus
lex_token m : "<>" --> tok_neq
lex_token m : "%" --> tok_rem
lex_token m : "+" --> tok_plus
lex_token m : "\]" --> tok_rbrack
lex_token m : "[)]" --> tok_rparen
lex_token m : ";" --> tok_semi
lex_token m : "*" --> tok_times

declare prec_let : Precedence
declare prec_apply : Precedence
declare prec_atom : Precedence

lex_prec right [prec_let]
lex_prec left [tok_semi; tok_let] > prec_let
lex_prec left [tok_id[s:s]; prec_atom] > tok_semi
lex_prec left [tok_else] > prec_atom
lex_prec left [tok_lt; tok_le; tok_gt; tok_ge; tok_eq; tok_neq] > tok_else
lex_prec left [tok_plus; tok_minus] > tok_lt
lex_prec left [tok_times; tok_div; tok_rem] > tok_plus
lex_prec left [tok_lbrack] > tok_times
lex_prec left [tok_lparen] > tok_lbrack
lex_prec right [prec_apply] > tok_lparen

declare m{'e} : Nonterminal
declare ast_exp{'e} : Nonterminal
declare tuple{'e} : Nonterminal
declare args{'e} : Nonterminal
declare params{'e} : Nonterminal
declare funs{'funs; 'pbunch; 'bodies} : Nonterminal
declare fn[f:s]{'params; 'e} : Nonterminal
declare MutFuns{'funs; 'pbunch; 'bodies; 'e} (* iform *)
declare var_term[v:s] (* iform *)
declare mcons{'v; 'rest} (* iform *)
declare mnil (* iform *)
declare process_functions{'R; 'funs; 'fvars; 'pbunch; 'fbodies} (* iform *)
declare project_functions{'R; 'fvars; 'body} (* iform *)
declare first_norec_bind_vars{'R; 'fvars; 'body} (* iform *)
declare first_bind_vars{'R; 'funs; 'params; 'body} (* iform *)
declare bind_vars{'R; 'funs; 'params; 'body} (* iform *)

parser m{'e} : m

(* Top-level *)
production m{AST{'e}} <-- ast_exp{'e}; tok_eof

iform dorp_m : m{'e} <--> 'e

(* Numbers *)
production ast_exp{IntExpr[i:n]} <-- tok_num[i:n]

(* Booleans *)
production ast_exp{TrueExpr} <-- tok_true
production ast_exp{FalseExpr} <-- tok_false

(* Variables *)
production ast_exp{VarExpr{'v}} <-- tok_id[v:s]

(* Anonymous functions *)
production ast_exp{LambdaExpr{v.'e}} %prec prec_let <--
   tok_fun; tok_id[v:s]; tok_arrow; ast_exp{'e}

(* Tuple expressions *)
production ast_exp{TupleExpr{'tuple}} <--
   tok_lparen; tuple{'tuple}; tok_rparen

(* Binary operations *)
production ast_exp{BinopExpr{AstAddOp; 'e1; 'e2}} <--
   ast_exp{'e1}; tok_plus; ast_exp{'e2}

production ast_exp{BinopExpr{AstSubOp; 'e1; 'e2}} <--
   ast_exp{'e1}; tok_minus; ast_exp{'e2}

production ast_exp{BinopExpr{AstMulOp; 'e1; 'e2}} <--
   ast_exp{'e1}; tok_times; ast_exp{'e2}

production ast_exp{BinopExpr{AstDivOp; 'e1; 'e2}} <--
   ast_exp{'e1}; tok_div; ast_exp{'e2}

(* Relational operations *)
production ast_exp{RelopExpr{AstLeOp; 'e1; 'e2}} <--
   ast_exp{'e1}; tok_le; ast_exp{'e2}

production ast_exp{RelopExpr{AstLtOp; 'e1; 'e2}} <--
   ast_exp{'e1}; tok_lt; ast_exp{'e2}

production ast_exp{RelopExpr{AstGeOp; 'e1; 'e2}} <--
   ast_exp{'e1}; tok_ge; ast_exp{'e2}

production ast_exp{RelopExpr{AstGtOp; 'e1; 'e2}} <--
   ast_exp{'e1}; tok_gt; ast_exp{'e2}

production ast_exp{RelopExpr{AstEqOp; 'e1; 'e2}} <--
   ast_exp{'e1}; tok_eq; ast_exp{'e2}

production ast_exp{RelopExpr{AstNeqOp; 'e1; 'e2}} <--
   ast_exp{'e1}; tok_neq; ast_exp{'e2}

(* Conditionals *)
production ast_exp{IfExpr{'e1; 'e2; 'e3}} <--
   tok_if; ast_exp{'e1}; tok_then; ast_exp{'e2}; tok_else; ast_exp{'e3}

(* Subscripting *)
production ast_exp{SubscriptExpr{'e1; 'e2}} <--
   ast_exp{'e1}; tok_lbrack; ast_exp{'e2}; tok_rbrack

(* Assignments *)
production ast_exp{AssignExpr{'e1; 'e2; 'e3; 'e4}} %prec prec_let <--
   ast_exp{'e1}; tok_lbrack; ast_exp{'e2}; tok_rbrack; tok_assign; ast_exp{'e3}; tok_semi; ast_exp{'e4}

(* Function application *)
production ast_exp{ApplyExpr{'f; 'args}} %prec prec_apply <--
   ast_exp{'f}; tok_lparen; args{'args}; tok_rparen

(* Let-definitions *)
production ast_exp{LetVarExpr{'e1; v. 'e2}} %prec prec_let <--
   tok_let; tok_id[v:s]; tok_eq; ast_exp{'e1}; tok_in; ast_exp{'e2}

(* Recursive functions *)
production ast_exp{MutFuns{'funs; 'pbunch; 'bodies; 'e}} %prec prec_let <--
   tok_let; tok_rec; funs{'funs; 'pbunch; 'bodies}; tok_in; ast_exp{'e}

(* Non-recursive functions *)
production ast_exp{
      AstLetRec{R. AstFields{
         AstFunDef{AstLabel[f:s]; first_norec_bind_vars{var_term["R"]; 'params; 'body}; AstEndDef}};
         R. project_functions{'R; mcons{var_term[f:s]; mnil}; 'rest}}
      } %prec prec_let <--
   tok_let; fn[f:s]{'params; 'body}; tok_in; ast_exp{'rest}

(* Tuples *)
production tuple{AstAllocTupleCons{'e; AstAllocTupleNil}} <-- ast_exp{'e}

production tuple{AstAllocTupleCons{'e; 'tuple}} <--
   ast_exp{'e}; tok_comma; tuple{'tuple}

(* Functions *)
production funs{mcons{var_term[f:s]; mnil}; mcons{'params; mnil}; mcons{'body; mnil}} <--
   fn[f:s]{'params; 'body}

production funs{mcons{var_term[f:s]; 'fvars}; mcons{'params; 'pbunch}; mcons{'body; 'fbodies}} <--
   fn[f:s]{'params; 'body}; tok_and; funs{'fvars; 'pbunch; 'fbodies}

(* Simple function *)
production fn[f:s]{'params; 'body} <--
   tok_id[f:s]; tok_lparen; params{'params}; tok_rparen; tok_eq; ast_exp{'body}

(* Function arguments *)
production args{AstArgCons{'e; AstArgNil}} <-- ast_exp{'e}

production args{AstArgCons{'e; 'args}} <--
   ast_exp{'e}; tok_comma; args{'args}

(* Function parameters *)
production params{mcons{var_term[v:s]; mnil}} <-- tok_id[v:s]

production params{mcons{var_term[v:s]; 'params}} <--
   tok_id[v:s]; tok_comma; params{'params}

iform mut_fun :
   MutFuns{'fvars; 'pbunch; 'fbodies; 'rest} <-->
   AstLetRec{R. AstFields{process_functions{'R; 'fvars; 'fvars; 'pbunch; 'fbodies}};
      R. project_functions{'R; 'fvars; 'rest}}

iform functs_nil : process_functions{'_1; '_2; mnil; mnil; mnil} <--> AstEndDef

iform functs_cons :
   process_functions{'R; 'funs; mcons{var_term[f:s]; 'fvars}; mcons{'params; 'pbunch}; mcons{'body; 'fbodies}} <-->
   AstFunDef{AstLabel[f:s];
      first_bind_vars{'R; 'funs; 'params; 'body};
      process_functions{'R; 'funs; 'fvars; 'pbunch; 'fbodies}}

iform first_bind_vars_nil : first_bind_vars{'R; 'fvars; mnil; 'body} <--> project_functions{'R; 'fvars; 'body}

iform first_bind_vars_cons :
   first_bind_vars{'R; 'fvars; mcons{var_term[v:s]; 'vars}; 'body} <-->
   FunLambdaExpr{v. bind_vars{'R; 'fvars; 'vars; 'body}}

iform bind_vars_nil : bind_vars{'R; 'fvars; mnil; 'body} <--> project_functions{'R; 'fvars; 'body}

iform bind_vars_cons :
   bind_vars{'R; 'fvars; mcons{var_term[v:s]; 'vars}; 'body} <-->
   LambdaExpr{v. bind_vars{'R; 'fvars; 'vars; 'body}}

iform norec_bind_nil : first_norec_bind_vars{'R; mnil; 'body} <--> 'body

iform norec_bind_cons :
   first_norec_bind_vars{'R; mcons{var_term[v:s]; 'vars}; 'body} <-->
   LambdaExpr{v. first_norec_bind_vars{'R; 'vars; 'body}}

iform project_nil: project_functions{'_1; mnil; 'rest} <--> 'rest

iform project_cons:
   project_functions{'R; mcons{var_term[f:s]; 'fvars}; 'rest} <-->
   AstLetFun{'R; AstLabel[f:s]; f. project_functions{'R; 'fvars; 'rest}}
