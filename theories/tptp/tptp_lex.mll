(*
 * Lexer for TPTP files.
 *)
{
open Printf
open Mp_debug

open Tptp_parse
}

rule main = parse
    [' ' '\010' '\013' '\009' '\012'] + 
    { main lexbuf }
  | ['A'-'Z' '\192'-'\214' '\216'-'\222' ]
    (['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255'
      '\'' '0'-'9' ]) *
      { Uid (Lexing.lexeme lexbuf) }

  | ['a'-'z']
    (['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255'
      '\'' '0'-'9' ]) *
      { match Lexing.lexeme lexbuf with
           "include" -> Include
         | "input_clause" -> Input_clause
         | name -> Lid name
      }
  | '(' 
    { LeftParen }
  | ')' 
    { RightParen }
  | '[' 
    { LeftBrack }
  | ']' 
    { RightBrack }
  | '\''  [^ '\''] * '\''
    { let s = Lexing.lexeme lexbuf in
	let s' = String.create (String.length s - 2) in
	   String.blit s 1 s' 0 (String.length s');
	   String s'
    }
  | "--" 
    { Negative }
  | "++" 
    { Positive }
  | ',' 
    { Comma }
  | '.' 
    { Dot }
  | '%' [^'\n'] *
    { main lexbuf }
  | eof
      { Eof }
  | _ 
      { eprintf "Undefined token '%s'%t" (Lexing.lexeme lexbuf) eflush;
	main lexbuf
      }

(*
 *
 *)
