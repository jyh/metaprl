(*
 * This file contains the primitive syntax and display
 * for ocaml terms.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
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
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

open Nl_debug
open Printf

open Refiner.Refiner

let _ =
   if !debug_load then
      eprintf "Loading Ocaml_base_df%t" eflush

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

(************************************************************************
 * DISPLAYS                                                             *
 ************************************************************************)

(*
 * Operators.
 *)
dform left_brack_df	: "["		= pushfont["bold"] `"[" popfont
dform right_brack_df	: "]"		= pushfont["bold"] `"]" popfont
dform left_array_df	: "[|"		= pushfont["bold"] `"[|" popfont
dform right_array_df	: "|]"		= pushfont["bold"] `"|]" popfont
dform left_stream_df	: "[<"		= pushfont["bold"] `"[<" popfont
dform right_stream_df	: ">]"		= pushfont["bold"] `">]" popfont
dform left_curly_df	: "{"		= pushfont["bold"] `"{" popfont
dform right_curly_df	: "}"		= pushfont["bold"] `"}" popfont
dform left_paren_df	: "("		= pushfont["bold"] `"(" popfont
dform right_paren_df	: ")"		= pushfont["bold"] `")" popfont

dform plus_df		: "+"		= pushfont["bold"] `"+" popfont
dform minus_df		: "-"		= pushfont["bold"] `"-" popfont
dform star_df		: "*"		= pushfont["bold"] `"*" popfont
dform slash_df		: "/"		= pushfont["bold"] `"/" popfont
dform mod_df_df    	: "mod"		= pushfont["bold"] `"mod" popfont

dform and_df		: "&"		= pushfont["bold"] `"&" popfont
dform or_df		: "or"		= pushfont["bold"] `"or" popfont
dform eq_df		: "="		= pushfont["bold"] `"=" popfont
dform eqeq_df		: "=="		= pushfont["bold"] `"==" popfont
dform colon_colon_df	: "::"		= pushfont["bold"] `"::" popfont
dform colon_eq_df	: ":="		= pushfont["bold"] `":=" popfont
dform dot_df		: "."		= pushfont["bold"] `"." popfont
dform array_sub_df	: ".("		= pushfont["bold"] `".(" popfont
dform string_sub_df	: ".["		= pushfont["bold"] `".[" popfont
dform coerce_df         : ":>"		= pushfont["bold"] `":>" popfont
dform semicolon_df	: ";"		= pushfont["bold"] `";" popfont
dform arrow_df		: "->"		= pushfont["bold"] `"->" popfont
dform pipe_df		: "|"		= pushfont["bold"] `"|" popfont
dform neq_df    	: "<>"		= pushfont["bold"] `"<>" popfont
dform colon_df          : ":"		= pushfont["bold"] `":" popfont
dform underscore_df	: "_"		= pushfont["bold"] `"_" popfont
dform hash_df		: "#"		= pushfont["bold"] `"#" popfont
dform quote_df		: "'"		= pushfont["bold"] `"'" popfont
dform backslash_df	: "\""		= pushfont["bold"] `"\"" popfont

dform if_df		: "_if"		= pushfont["bold"] `"if" popfont
dform then_df		: "_then"	= pushfont["bold"] `"then" popfont
dform else_df		: "_else"	= pushfont["bold"] `"else" popfont

dform for_df		: "_for"	= pushfont["bold"] `"for" popfont
dform while_df		: "_while"	= pushfont["bold"] `"while" popfont
dform to_df		: "_to"		= pushfont["bold"] `"to" popfont
dform downto_df		: "_downto"	= pushfont["bold"] `"downto" popfont
dform do_df		: "_do"		= pushfont["bold"] `"do" popfont
dform done_df		: "_done"	= pushfont["bold"] `"done" popfont

dform new_df		: "_new"	= pushfont["bold"] `"new" popfont
dform fun_df		: "_fun"	= pushfont["bold"] `"fun" popfont
dform match_df		: "_match"	= pushfont["bold"] `"match" popfont
dform try_df		: "_try"	= pushfont["bold"] `"try" popfont
dform type_df		: "_type"	= pushfont["bold"] `"type" popfont
dform exception_df	: "_exception"	= pushfont["bold"] `"exception" popfont
dform let_df		: "_let"	= pushfont["bold"] `"let" popfont
dform letrec_df		: "_letrec"	= pushfont["bold"] `"let rec" popfont
dform in_df		: "_in"		= pushfont["bold"] `"in" popfont
dform and_df		: "_and"	= pushfont["bold"] `"and" popfont
dform with_df		: "_with"	= pushfont["bold"] `"with" popfont
dform val_df		: "_val"	= pushfont["bold"] `"val" popfont
dform as_df		: "_as"		= pushfont["bold"] `"as" popfont
dform external_df	: "_external"	= pushfont["bold"] `"of" popfont
dform of_df		: "_of"		= pushfont["bold"] `"external" popfont

dform module_df		: "_module"	= pushfont["bold"] `"module" popfont
dform moduletype_df	: "_moduletype"	= pushfont["bold"] `"module type" popfont
dform open_df		: "_open"	= pushfont["bold"] `"open" popfont
dform sig_df		: "_sig"	= pushfont["bold"] `"sig" popfont
dform struct_df		: "_struct"	= pushfont["bold"] `"struct" popfont
dform functor_df	: "_functor"	= pushfont["bold"] `"functor" popfont
dform end_df		: "_end"	= pushfont["bold"] `"end" popfont

dform push_ident_df     : push_indent   = pushm[3]

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
