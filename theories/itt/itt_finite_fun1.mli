(*
 * Finite functions.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
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
extends Itt_nat

(*
 * Type of simple finite functions.
 *)
declare simple_ffun{'T}

(*
 * Total number of alements.
 *)
declare length_ffun{'f}

(*
 * Add an element.
 *)
declare add_ffun{'f; 'x}

(*
 * Get an element.
 *)
declare apply_ffun{'f; 'i}

(************************************************************************
 * Grammar.
 *)
declare tok_sff      : Terminal
declare tok_plus_eq  : Terminal

lex_token itt : "sff"  --> tok_sff
lex_token itt : "+="   --> tok_plus_eq

lex_prec right [tok_sff] = prec_not

production itt_term{simple_ffun{'t}} <--
   tok_sff; itt_term{'t}

production itt_term{length_ffun{'f}} <--
   tok_sff; tok_pipe; itt_term{'f}; tok_pipe

production itt_term{add_ffun{'f; 'x}} <--
   tok_sff; tok_left_curly; itt_term{'f}; tok_plus_eq; itt_term{'x}; tok_right_curly

production itt_term{apply_ffun{'f; 'x}} <--
   tok_sff; tok_left_curly; itt_term{'f}; tok_at; itt_term{'x}; tok_right_curly

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
