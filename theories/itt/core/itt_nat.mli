(*
 * Natural numbers.
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
 * Author: Alexei Kopylov
 * @email{kopylov@cs.cornell.edu}
 * @end[license]
 *)
extends Itt_int_ext

open Basic_tactics

val ind_term : term
val is_ind_term : term -> bool
val dest_ind : term -> term * term * var * var * term
val mk_ind_term : term -> term -> var -> var -> term -> term

define unfold_nat :
   nat <--> ({x:int | 'x>=0})

define unfold_nat_plus :
   nat_plus <--> ({x:int | 'x>0})

define unfold_finite_nat : nat{'k} <--> int_seg{0; 'k}

define unfoldInd : ind{'n; 'base; k,l. 'up['k;'l]} <-->
                   ind{'n; i,j.it; 'base; k,l . 'up['k;'l]}

define iform unfoldInd1 : ind{'n; 'base; l. 'up['l]} <-->
                    ind{'n; 'base; k,l . 'up['l]}

topval foldInd : conv

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval natBackInductionT : term -> tactic

topval positiveRule1T : tactic
topval positiveRule2T : tactic

(************************************************************************
 * Grammar for integer ranges.
 *)
declare tok_dot_dot    : Terminal

lex_token xterm : "[.][.]"   --> tok_dot_dot

production xterm_term{{ i: int | 'j <= 'i & 'i <= 'k }} <--
   tok_left_brace; xterm_apply_term{'j}; tok_dot_dot; xterm_apply_term{'k}; tok_right_brace

production xterm_term{{ i: int | 'j <= 'i & 'i < 'k }} <--
   tok_left_brace; xterm_apply_term{'j}; tok_dot_dot; xterm_apply_term{'k}; tok_minus; tok_right_brace

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
