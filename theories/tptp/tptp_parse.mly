/*
 * This is the parser for TPTP files.
 */

%{

open Tptp_type
%}

%token Eof
%token End_of_include
%token Include
%token Input_clause
%token LeftParen
%token RightParen
%token LeftBrack
%token RightBrack
%token Negative
%token Positive
%token Comma
%token Dot
%token <string> String
%token <string> Uid
%token <string> Lid

%start program
%type <Tptp_type.clause list * Tptp_type.file_command> program

%%

program: 
	  clauses Eof
	  { List.rev $1, FileComplete }
        | clauses Include LeftParen String RightParen Dot
          { List.rev $1, FileInclude $4 }
        | clauses error
	  { List.rev $1, FileError }
       ;

clauses:  /* empty */
	  { [] }
        | clauses clause
          { $2 :: $1 }

clause: Input_clause LeftParen Lid Comma Lid Comma clause_info RightParen Dot
          { { clause_name = $3;
	      clause_type =
	         (match $5 with
                     "axiom"
                   | "hypothesis" ->
	               Axiom
                   | "conjecture" ->
	               Goal
                   | name ->
                     raise Parse_error);
	      clause_expr = $7
            }
          }                  
        ;

clause_info : LeftBrack clause_parts RightBrack
          { $2 }
        ;

clause_parts :
	  clause_part
          { [$1] }
        | clause_parts Comma clause_part
          { $1 @ [$3] }
        ;

clause_part :
 	  Positive expr
          { $2 }
        | Negative expr
          { NegExpr $2 }
        ;

exprs :
	  expr
          { [$1] }
        | exprs Comma expr
          { $1 @ [$3] }
        ;

expr :
	  Lid
          { FunExpr ($1, []) }
        | Uid
          { UidExpr $1 }
        | Lid LeftParen exprs RightParen
          { FunExpr ($1, $3) }
        ;
