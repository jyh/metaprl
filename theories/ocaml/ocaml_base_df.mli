(*
 * This file contains the primitive syntax and display
 * for ocaml terms.
 *)

(************************************************************************
 * DISPLAY UTILITIES                                                    *
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

(*
 * $Log$
 * Revision 1.1  1998/02/18 18:47:07  jyh
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
