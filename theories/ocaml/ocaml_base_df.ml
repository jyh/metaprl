(*
 * This file contains the primitive syntax and display
 * for ocaml terms.
 *)

(************************************************************************
 * DISPLAY TERMS                                                        *
 ************************************************************************)

(*
 * Operators.
 *)
declare "["
declare "]"
declare "[|"
declare "|]"
declare "[<"
declare ">]"
declare "{"
declare "}"
declare "("
declare ")"

declare "+"
declare "-"
declare "*"
declare "/"
declare "mod"

declare "&"
declare "or"
declare "="
declare "=="
declare "::"
declare ":="
declare "."
declare ".("
declare ".["
declare ":>"
declare ";"
declare "->"
declare "|"
declare "<>"
declare ":"
declare "_"
declare "#"
declare "'"
declare "\""

declare "if"
declare "then"
declare "else"

declare "for"
declare "while"
declare "to"
declare "downto"
declare "do"
declare "done"

declare "type"
declare "exception"
declare "let"
declare "letrec"
declare "in"
declare "and"
declare "with"
declare "val"
declare "as"
declare "external"
declare "of"

declare "module"
declare "moduletype"
declare "open"
declare "sig"
declare "struct"
declare "functor"
declare "end"

declare push_indent

(*
 * Display control tags.
 *)
declare patt_format

(************************************************************************
 * DISPLAYS                                                             *
 ************************************************************************)

(*
 * Operators.
 *)
dform "["		= pushfont["bold"] `"[" popfont
dform "]"		= pushfont["bold"] `"]" popfont
dform "[|"		= pushfont["bold"] `"[|" popfont
dform "|]"		= pushfont["bold"] `"|]" popfont
dform "[<"		= pushfont["bold"] `"[<" popfont
dform ">]"		= pushfont["bold"] `">]" popfont
dform "{"		= pushfont["bold"] `"{" popfont
dform "}"		= pushfont["bold"] `"}" popfont
dform "("		= pushfont["bold"] `"(" popfont
dform ")"		= pushfont["bold"] `")" popfont

dform "+"		= pushfont["bold"] `"+" popfont
dform "-"		= pushfont["bold"] `"-" popfont
dform "*"		= pushfont["bold"] `"*" popfont
dform "/"		= pushfont["bold"] `"/" popfont
dform "mod"		= pushfont["bold"] `"mod" popfont

dform "&"		= pushfont["bold"] `"&" popfont
dform "or"		= pushfont["bold"] `"or" popfont
dform "="		= pushfont["bold"] `"=" popfont
dform "=="		= pushfont["bold"] `"==" popfont
dform "::"		= pushfont["bold"] `"::" popfont
dform ":="		= pushfont["bold"] `":=" popfont
dform "."		= pushfont["bold"] `"." popfont
dform ".("		= pushfont["bold"] `".(" popfont
dform ".["		= pushfont["bold"] `".[" popfont
dform ":>"		= pushfont["bold"] `":>" popfont
dform ";"		= pushfont["bold"] `";" popfont
dform "->"		= pushfont["bold"] `"->" popfont
dform "|"		= pushfont["bold"] `"|" popfont
dform "<>"		= pushfont["bold"] `"<>" popfont
dform ":"		= pushfont["bold"] `":" popfont
dform "_"		= pushfont["bold"] `"_" popfont
dform "#"		= pushfont["bold"] `"#" popfont
dform "'"		= pushfont["bold"] `"'" popfont
dform "\""		= pushfont["bold"] `"\"" popfont

dform "if"		= pushfont["bold"] `"if" popfont
dform "then"		= pushfont["bold"] `"then" popfont
dform "else"		= pushfont["bold"] `"else" popfont

dform "for"		= pushfont["bold"] `"for" popfont
dform "while"		= pushfont["bold"] `"while" popfont
dform "to"		= pushfont["bold"] `"to" popfont
dform "downto"		= pushfont["bold"] `"downto" popfont
dform "do"		= pushfont["bold"] `"do" popfont
dform "done"		= pushfont["bold"] `"done" popfont

dform "type"		= pushfont["bold"] `"type" popfont
dform "exception"	= pushfont["bold"] `"exception" popfont
dform "let"		= pushfont["bold"] `"let" popfont
dform "letrec"		= pushfont["bold"] `"let rec" popfont
dform "in"		= pushfont["bold"] `"in" popfont
dform "and"		= pushfont["bold"] `"and" popfont
dform "with"		= pushfont["bold"] `"with" popfont
dform "val"		= pushfont["bold"] `"val" popfont
dform "as"		= pushfont["bold"] `"as" popfont
dform "external"	= pushfont["bold"] `"of" popfont
dform "of"		= pushfont["bold"] `"external" popfont

dform "module"		= pushfont["bold"] `"module" popfont
dform "moduletype"	= pushfont["bold"] `"module type" popfont
dform "open"		= pushfont["bold"] `"open" popfont
dform "sig"		= pushfont["bold"] `"sig" popfont
dform "struct"		= pushfont["bold"] `"struct" popfont
dform "functor"		= pushfont["bold"] `"functor" popfont
dform "end"		= pushfont["bold"] `"end" popfont

dform push_indent       = pushm[3]

(*
 * $Log$
 * Revision 1.1  1998/02/18 18:47:05  jyh
 * Initial ocaml semantics.
 *
 * Revision 1.1  1998/02/13 16:02:06  jyh
 * Partially implemented semantics for caml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
