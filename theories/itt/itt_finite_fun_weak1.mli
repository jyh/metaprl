(*
 * Finite functions.  This version has much the same syntax and
 * theorems as the strict finite function Itt_finite_fun1, but it
 * uses an infinite function to make the well-formedness goals
 * easier.
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
extends Itt_finite_fun1

(*
 * Type of simple finite functions.
 *)
declare simple_ifun{'T}

(*
 * An initial empty function.
 *)
declare empty_ifun{'x}

(*
 * Total number of alements.
 *)
declare length_ifun{'f}

(*
 * Add an element.
 *)
declare add_ifun{'f; 'x}

(*
 * Get an element.
 *)
declare apply_ifun{'f; 'i}

(************************************************************************
 * Grammar.
 *)
declare tok_sif      : Terminal

lex_token itt : "sif"  --> tok_sif

lex_prec right [tok_sif] = prec_not

production itt_term{simple_ifun{'t}} <--
   tok_sif; itt_term{'t}

production itt_term{empty_ifun{'x}} <--
   tok_sif; tok_left_curly; itt_term{'x}; tok_right_curly

production itt_term{length_ifun{'f}} <--
   tok_sif; tok_pipe; itt_term{'f}; tok_pipe

production itt_term{add_ifun{'f; 'x}} <--
   tok_sif; tok_left_curly; itt_term{'f}; tok_plus_eq; itt_term{'x}; tok_right_curly

production itt_term{apply_ifun{'f; 'x}} <--
   tok_sif; tok_left_curly; itt_term{'f}; tok_at; itt_term{'x}; tok_right_curly

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
