(*
 * Resources for parsing and lexing.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2004 Mojave Group, Caltech
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
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
open Lm_printf
open Lm_symbol

open Refiner.Refiner.TermType
open Refiner.Refiner.TermShape

(*
 * Lexer and parser.
 *)
type t

(*
 * Precedence for tokens in the grammar.
 *)
type assoc = Lm_parser.assoc =
   LeftAssoc
 | RightAssoc
 | NonAssoc
 | NoneAssoc

type precedence

(*
 * The source locations are used to identify the actions.
 * CAUTION: it is important that every token and production
 * have a unique id.
 *)
type id = Lexing.position

(*
 * Add a lexer token.
 * If the term option is None, this token is ignored.
 *)
val add_token      : t -> id -> string -> term option -> t

(*
 * Add a production.
 *)
val add_production : t -> id -> term list -> shape option -> term -> t

(*
 * Union of two grammars.
 *)
val union          : t -> t -> t

(*
 * Precedence operations.
 *)
val prec_min        : precedence
val prec_max        : precedence

val empty           : t
val is_empty        : t -> bool

val find_prec       : t -> shape -> precedence
val create_prec_new : t -> assoc -> t * precedence
val create_prec_lt  : t -> shape -> assoc -> t * precedence
val create_prec_gt  : t -> shape -> assoc -> t * precedence

val add_prec        : t -> precedence -> shape -> t

(*
 * Start symbols.
 *)
val add_start       : t -> shape -> t
val get_start       : t -> shape list

(*
 * Input forms.
 *)
val add_iform       : t -> id -> term -> term -> t

(*
 * Build the machines and check for errors.
 * This is moderately expensive.
 *)
val compile         : t -> unit

(*
 * Build the machines and check for errors,
 * but eliminate the iform table since it can't be marshaled.
 * In addition, the grammar is given a name.
 *)
val prepare_to_marshal : t -> string -> t

(*
 * Check if the grammar has been changed since the
 * last time it was given a name.
 *)
val is_modified        : t -> bool

(*
 * Print (for debugging).
 *)
val pp_print_grammar : out_channel -> t -> unit

(*
 * Parse a string.
 *)
val parse           : t -> shape -> Lexing.position -> string -> term

(*
 * Stateful versions.
 * The Filter_cache_fun should try and make sure these functions
 * are called each time the grammar is modified.
 *)
val set_grammar     : t -> unit
val set_start       : string -> shape -> unit
val term_of_string  : string -> Lexing.position -> string -> term

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
