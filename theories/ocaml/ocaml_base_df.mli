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

declare "_if"
declare "_then"
declare "_else"

declare "_for"
declare "_while"
declare "_to"
declare "_downto"
declare "_do"
declare "_done"

declare "_new"
declare "_fun"
declare "_match"
declare "_try"
declare "_type"
declare "_exception"
declare "_let"
declare "_letrec"
declare "_in"
declare "_and"
declare "_with"
declare "_val"
declare "_as"
declare "_external"
declare "_of"

declare "_module"
declare "_moduletype"
declare "_open"
declare "_sig"
declare "_struct"
declare "_functor"
declare "_end"

declare push_indent

(*
 * Display control tags.
 *)
declare patt_format

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
