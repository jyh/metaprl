(*
 * Rules for dependent product.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
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
 *
 *)
extends Itt_equal
extends Itt_struct
extends Itt_subtype

open Lm_symbol

open Refiner.Refiner.TermType

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(* declare prod{'A; 'B} *)
declare prod{'A; x. 'B['x]}
declare prod{'A; 'B}
declare pair{'a; 'b}
declare spread{'e; u, v. 'b['u; 'v]}

define iform unfold_spread3:  spread{'e; u1,u2,u3. 'b['u1; 'u2; 'u3]} <-->  spread{'e; u1,v. spread{'v; u2,u3. 'b['u1; 'u2; 'u3]}}

define unfoldFst : fst{'e} <--> spread{'e; u, v. 'u}
define unfoldSnd : snd{'e} <--> spread{'e; u, v. 'v}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_prod
prec prec_spread

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

(*
 * Reduction on spread:
 * spread(u, v; a, b. c[a, b]) <--> c[u, v]
 *)
rewrite reduceSpread : spread{'u, 'v; a, b. 'c['a; 'b]} <--> 'c['u; 'v]
rewrite reduceFst : fst{pair{'a; 'b}} <--> 'a
rewrite reduceSnd : snd{pair{'a; 'b}} <--> 'b

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext x:A # B
 * by productFormation A
 * H >- A = A in Ui
 * H, x:A >- Ui ext B
 *)
rule productFormation 'A :
   sequent { <H> >- 'A in univ[i:l] } -->
   sequent { <H>; x: 'A >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] }

(*
 * H >- x1:A1 # B1 = x2:A2 # B2 in Ui
 * by productEquality
 * H >- A1 = A2 in Ui
 * H, y:A1 >- B1[y] = B2[y] in Ui
 *)
rule productEquality :
   sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   sequent { <H>; y: 'A1 >- 'B1['y] = 'B2['y] in univ[i:l] } -->
   sequent { <H> >- x1:'A1 * 'B1['x1] = x2:'A2 * 'B2['x2] in univ[i:l] }

(*
 * Typehood.
 *)
rule productType :
   sequent { <H> >- "type"{'A1} } -->
   sequent { <H>; x: 'A1 >- "type"{'A2['x]} } -->
   sequent { <H> >- "type"{y:'A1 * 'A2['y]} }

(*
 * H >- x:A * B ext (a, b)
 * by pairFormation a
 * H >- a = a in A
 * H >- B[a] ext b
 * H, y:A >- B[y] = B[y] in Ui
 *)
rule pairFormation 'a :
   sequent { <H> >- 'a in 'A } -->
   sequent { <H> >- 'B['a] } -->
   sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- x:'A * 'B['x] }

(*
 * H >- (a1, b1) = (a2, b2) in x:A * B
 * by pairEquality
 * H >- a1 = a2 in A
 * H >- b1 = b2 in B[a1]
 * H, y:A >- B[y] = B[y] in Ui
 *)
rule pairEquality :
   sequent { <H> >- 'a1 = 'a2 in 'A } -->
   sequent { <H> >- 'b1 = 'b2 in 'B['a1] } -->
   sequent { <H>; y: 'A >- "type"{'B['y]} } -->
   sequent { <H> >- ('a1, 'b1) = ('a2, 'b2) in x:'A * 'B['x] }

(*
 * H, x:A * B[x], J[x] >- T[x] ext spread(x; u, v. t[u, v])
 * by productElimination
 * H, x:A * B, u:A, v:B[u], J[u, v] >- T[u, v] ext t[u, v]
 *)
rule productElimination 'H :
   sequent { <H>; u: 'A; v: 'B['u]; <J['u, 'v]> >- 'T['u, 'v] } -->
   sequent { <H>; z: x:'A * 'B['x]; <J['z]> >- 'T['z] }

(*
 * H >- spread(e1; u1, v1. b1) = spread(e2; u2, v2. b2) in T[e1]
 * by spreadEquality (w:A * B)
 * H >- e1 = e2 in w:A * B
 * H, u:A, v: B[u], a: e1 = (u, v) in w:A * B >- b1[u; v] = b2[u; v] in T[u, v]
 *)
rule spreadEquality bind{z. 'T['z]} (w:'A * 'B['w]) :
   sequent { <H> >- 'e1 = 'e2 in w:'A * 'B['w] } -->
   sequent { <H>; u: 'A; v: 'B['u]; a: 'e1 = ('u, 'v) in w:'A * 'B['w] >-
             'b1['u; 'v] = 'b2['u; 'v] in 'T['u, 'v] } -->
   sequent { <H> >- spread{'e1; u1, v1. 'b1['u1; 'v1]} = spread{'e2; u2, v2. 'b2['u2; 'v2]} in 'T['e1] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val dprod_term : term
val is_dprod_term : term -> bool
val dest_dprod : term -> var * term * term
val mk_dprod_term : var -> term -> term -> term

val prod_term : term
val is_prod_term : term -> bool
val dest_prod : term -> term * term
val mk_prod_term : term -> term -> term

val pair_term : term
val is_pair_term : term -> bool
val dest_pair : term -> term * term
val mk_pair_term : term -> term -> term

val spread_term : term
val is_spread_term : term -> bool
val dest_spread : term -> var * var * term * term
val mk_spread_term : var -> var -> term -> term -> term

(************************************************************************
 * Grammar.
 *)
declare tok_Prod      : Terminal

lex_token xterm : "Prod" --> tok_Prod

declare xterm_tuple{'args} : Nonterminal

production xterm_simple_term{'t} <--
   tok_left_paren; xterm_tuple{'t}; tok_right_paren

production xterm_tuple{pair{'t1; 't2}} <--
   xterm_term{'t1}; tok_comma; xterm_term{'t2}

production xterm_tuple{pair{'t1; 't2}} <--
   xterm_term{'t1}; tok_comma; xterm_tuple{'t2}

production xterm_term{'t1 * 't2} <--
   xterm_term{'t1}; tok_star; xterm_term{'t2}

production xterm_term{x: 't1 * 't2} <--
   tok_Prod; tok_id[x:s]; tok_colon; xterm_apply_term{'t1}; tok_star; xterm_term{'t2}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
