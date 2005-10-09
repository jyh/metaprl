(*
 * Reduction.
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
extends Pmn_core_tast

(*
 * The expression 'e is a value.
 *)
declare value{'e : Exp} : Prop

(*
 * One-step reduction relation.
 *)
declare reducesto{'e1 : Exp; 'e2 : Exp} : Prop

(************************************************************************
 * Grammar.
 *)
declare tok_value     : Terminal

declare tok_reducesto : Terminal

lex_token itt : "value"  --> tok_value
lex_token itt : "==>"    --> tok_reducesto

lex_prec nonassoc [tok_value] = prec_in
lex_prec nonassoc [tok_reducesto] = prec_iff

production itt_term{value{'e}} <--
    tok_value; itt_term{'e}

production itt_term{reducesto{'e1; 'e2}} <--
    itt_term{'e1}; tok_reducesto; itt_term{'e2}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
