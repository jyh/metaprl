(*
 * Some more about integers
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
 * Author: Yegor Bryukhov
 * @email{ynb@mail.ru}
 *)
extends Itt_equal
extends Itt_logic
extends Itt_bool
extends Itt_int_base

open Basic_tactics

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "mul"{'a; 'b}
declare "div"{'a; 'b}
declare "rem"{'a; 'b}

(*
 Definitions of >b <=b >=b
 *)

define unfold_gt_bool :
   gt_bool{'a; 'b} <--> lt_bool{'b; 'a}

define unfold_le_bool :
   le_bool{'a; 'b} <--> bnot{lt_bool{'b; 'a}}

define unfold_ge_bool :
   ge_bool{'a; 'b} <--> bnot{lt_bool{'a; 'b}}

define unfold_bneq_int :
   bneq_int{'a; 'b} <--> bnot{beq_int{'a; 'b}}

(*
 Prop-int-relations definitions
 *)

define unfold_gt :
   gt{'a; 'b} <--> ('b < 'a)

(*
Switching to define-version to provide the same behaviour as bool-relations,
i.d. rewritability of <= in the same extent as of <

rewrite unfold_le :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'a <= 'b <--> ('a < 'b) \/ ('a = 'b in int) }

rewrite unfold_ge :
   [wf] sequent { <H> >- a in int } -->
   [wf] sequent { <H> >- b in int } -->
   sequent { <H> >- 'a >= 'b <--> ('a < 'b) \/ ('a = 'b in int) }
*)

define unfold_le :
   le{'a; 'b} <--> "assert"{le_bool{'a; 'b}}

define unfold_ge :
   ge{'a; 'b} <--> ('b <= 'a)

define unfold_neq_int :
   nequal{'a; 'b} <--> "assert"{bneq_int{'a; 'b}}

define unfold_int_seg :
   int_seg{'i; 'j} <--> {x:int | 'x >= 'i & 'x < 'j}

define unfold_max: max{'i;'j} <--> if 'i<@ 'j then 'j else 'i

define unfold_min: min{'i;'j} <--> if 'i<@ 'j then 'i else 'j

define unfold_abs : abs{'a} <--> ind{'a;x,y.(-'a);0;x,y.'a}
(*if 'a <@ 0 then -'a else 'a*)

define unfold_sign : sign{'a} <--> ind{'a;x,y.(-1);0;x,y.1}
(*if 'a <@ 0 then number[(-1):n] else if 0 <@ 'a then 1 else 0*)

topval fold_le : conv
topval fold_ge : conv

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_mul

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

topval fold_bneq_int : conv
topval fold_neq_int : conv

topval reduce_mul: conv
topval reduce_div: conv
topval reduce_rem: conv

val bneq_int_term : term
val is_bneq_int_term : term -> bool
val mk_bneq_int_term : term -> term -> term
val dest_bneq_int : term -> term * term

val le_term : term
val is_le_term : term -> bool
val mk_le_term : term -> term -> term
val dest_le : term -> term * term

val ge_term : term
val is_ge_term : term -> bool
val mk_ge_term : term -> term -> term
val dest_ge : term -> term * term

val gt_term : term
val is_gt_term : term -> bool
val mk_gt_term : term -> term -> term
val dest_gt : term -> term * term

val mul_term : term
val is_mul_term : term -> bool
val mk_mul_term : term -> term -> term
val dest_mul : term -> term * term

val div_term : term
val is_div_term : term -> bool
val mk_div_term : term -> term -> term
val dest_div : term -> term * term

val rem_term : term
val is_rem_term : term -> bool
val mk_rem_term : term -> term -> term
val dest_rem : term -> term * term

val neq_int_term : term
val is_neq_int_term : term -> bool
val mk_neq_int_term : term -> term -> term
val dest_neq_int : term -> term * term

rule beq_int_is_false :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'a <> 'b } -->
   sequent { <H> >- beq_int{'a; 'b} ~ bfalse }

topval beq_int_is_falseC: conv

rule not_nequal :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- not{'a <> 'b} } -->
   sequent { <H> >- 'a = 'b in int }

topval notNequalT: tactic

rule ge_addWeakMono :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- ('a +@ 'c) >= ('b +@ 'c) }

rule ge_addWeakMono2 :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- ('c +@ 'a) >= ('c +@ 'b) }

rule ge_Transit 'b :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- 'b >= 'c } -->
   sequent { <H> >- 'a >= 'c }

rule ge_addMono :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   [wf] sequent { <H> >- 'd in int } -->
   sequent { <H> >- 'a >= 'b } -->
   sequent { <H> >- 'c >= 'd } -->
   sequent { <H> >- ('a +@ 'c) >= ('b +@ 'd) }

topval ge_to_leftC : conv
topval lt_bool2le_boolC: conv
topval le_bool2lt_boolC: conv

rule mul_wf :
   [wf] sequent { <H> >- 'a = 'a1 in int } -->
   [wf] sequent { <H> >- 'b = 'b1 in int } -->
   sequent { <H> >- 'a *@ 'b = 'a1 *@ 'b1 in int }

rule mul_Commut :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a *@ 'b) ~ ('b *@ 'a) }

topval mul_CommutC: conv

rule mul_Assoc :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a *@ ('b *@ 'c)) ~ (('a *@ 'b) *@ 'c) }

topval mul_AssocC: conv
topval mul_Assoc2C: conv

rule mul_add_Distrib :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a *@ ('b +@ 'c)) ~ (('a *@ 'b) +@ ('a *@ 'c)) }

topval mul_add_DistribC: conv

rewrite mul_add_Distrib2C :
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   (('a *@ 'b) +@ ('a *@ 'c)) <--> ('a *@ ('b +@ 'c))

rewrite mul_add_Distrib3C :
   ('a in int) -->
   ('b in int) -->
   ('c in int) -->
   (('a +@ 'b) *@ 'c) <--> (('a *@ 'c) +@ ('b *@ 'c))

rule mul_Id :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- (1 *@ 'a) ~ 'a }

topval mul_IdC: conv
topval mul_Id2C: conv
topval mul_Id3C: conv

rule mul_Zero :
   [wf] sequent { <H> >- 'a in int } -->
   sequent { <H> >- (0 *@ 'a) ~ 0 }

rewrite uni2negative1C :
	('a in int) -->
	(- 'a) <--> ((-1) *@ 'a)

rule lt_mulPositMonoEq 'c :
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{'a; 'b} = lt_bool{('c *@ 'a); ('c *@ 'b) } in bool }

rule lt_mulPositMono 'c :
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{'a; 'b} ~ lt_bool{('c *@ 'a); ('c *@ 'b) } }

topval lt_mulPositMonoC : term -> conv

rule mul_uni_Assoc :
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a *@ (- 'b)) ~ ((- 'a) *@ 'b) }

topval mul_uni_AssocC : conv

rule lt_mulNegMono 'c :
   sequent { <H> >- 'c < 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- lt_bool{'a; 'b} ~ lt_bool{('c *@ 'b) ; ('c *@ 'a)} }

topval lt_mulNegMonoC : term -> conv

rule rem_baseReduce :
   sequent { <H> >- 0 <= 'a } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a %@ 'b) ~ 'a }

topval rem_baseReduceC : conv

rule rem_neg :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a %@ 'b) ~ ('a %@ (-'b)) }

topval rem_negC : conv

rule rem_indReduce :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ((('a *@ 'b) +@ 'c) %@ 'b) ~ ('c %@ 'b) }

topval rem_indReduceC : conv

rule rem_wf :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a %@ 'b) in int }

rule div_baseReduce :
   sequent { <H> >- 0 <= 'a } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a /@ 'b) ~ 0 }

topval div_baseReduceC  : conv

rule div_neg :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- ('a /@ 'b) ~ ((-'a) /@ (-'b)) }

topval  div_negC : conv

rule div_indReduce :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ((('a *@ 'b) +@ 'c) /@ 'b) ~ ('a +@ ('c /@ 'b)) }

topval div_indReduceC  : conv

rule div_wf :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   sequent { <H> >- 'a /@ 'b in int }

rule div_remProperty :
   sequent { <H> >- 'b <> 0 } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
	sequent { <H> >- ('a %@ 'b) +@ ('a /@ 'b) *@ 'b = 'a in int }

rule lt_divMono 'b :
   sequent { <H> >- 0 < 'c } -->
   sequent { <H> >- 'a < 'b } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- 'a /@ 'c <= 'b /@ 'c }

rule add_divReduce :
   sequent { <H> >- 0 < 'a } -->
   sequent { <H> >- 0 < 'b } -->
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- ('a /@ 'c) +@ ('b /@ 'c) <= ('a +@ 'b) /@ 'c }

rule div_Assoc :
   sequent { <H> >- 0 <= 'a } -->
   sequent { <H> >- 0 < 'b } -->
   sequent { <H> >- 0 < 'c } -->
   [wf] sequent { <H> >- 'a in int } -->
   [wf] sequent { <H> >- 'b in int } -->
   [wf] sequent { <H> >- 'c in int } -->
   sequent { <H> >- (('a /@ 'b) /@ 'c) ~ ('a /@ ('b *@ 'c)) }

topval div_AssocC : conv

topval fold_int_seg : conv

(************************************************************************
 * Grammar.
 *)
declare tok_le      : Terminal
declare tok_ge      : Terminal
declare tok_eqeq    : Terminal

declare tok_lt_bool : Terminal
declare tok_gt_bool : Terminal
declare tok_le_bool : Terminal
declare tok_ge_bool : Terminal
declare tok_eq_bool : Terminal

declare tok_add     : Terminal
declare tok_sub     : Terminal
declare tok_mul     : Terminal
declare tok_div     : Terminal

lex_token xterm : "<="    --> tok_le
lex_token xterm : ">="    --> tok_ge
lex_token xterm : "=="    --> tok_eqeq

lex_token xterm : "<b"    --> tok_lt_bool
lex_token xterm : ">b"    --> tok_gt_bool
lex_token xterm : "<=b"   --> tok_le_bool
lex_token xterm : ">=b"   --> tok_ge_bool
lex_token xterm : "==b"   --> tok_eq_bool

lex_token xterm : "+@"    --> tok_add
lex_token xterm : "-@"    --> tok_sub
lex_token xterm : "*@"    --> tok_mul
lex_token xterm : "/@"    --> tok_div

lex_prec nonassoc [tok_lt; tok_le; tok_gt; tok_ge; tok_eqeq] = prec_rel
lex_prec nonassoc [tok_lt_bool; tok_gt_bool; tok_le_bool; tok_ge_bool; tok_eq_bool] = prec_rel
lex_prec left [tok_add; tok_sub] = prec_add
lex_prec left [tok_mul; tok_div] = prec_mul

(*
 * Propositions.
 *)
production xterm_term{'i < 'j} <--
   xterm_term{'i}; tok_lt; xterm_term{'j}

production xterm_term{'i > 'j} <--
   xterm_term{'i}; tok_gt; xterm_term{'j}

production xterm_term{'i <= 'j} <--
   xterm_term{'i}; tok_le; xterm_term{'j}

production xterm_term{'i >= 'j} <--
   xterm_term{'i}; tok_ge; xterm_term{'j}

production xterm_term{'i = 'j in int} <--
   xterm_term{'i}; tok_eqeq; xterm_term{'j}

(*
 * Boolean expressions.
 *)
production xterm_term{lt_bool{'i; 'j}} <--
   xterm_term{'i}; tok_lt_bool; xterm_term{'j}

production xterm_term{gt_bool{'i; 'j}} <--
   xterm_term{'i}; tok_gt_bool; xterm_term{'j}

production xterm_term{le_bool{'i; 'j}} <--
   xterm_term{'i}; tok_le_bool; xterm_term{'j}

production xterm_term{ge_bool{'i; 'j}} <--
   xterm_term{'i}; tok_ge_bool; xterm_term{'j}

production xterm_term{beq_int{'i; 'j}} <--
   xterm_term{'i}; tok_eq_bool; xterm_term{'j}

(*
 * Arithmetic.
 *)
production xterm_term{'i +@ 'j} <--
   xterm_term{'i}; tok_add; xterm_term{'j}

production xterm_term{'i -@ 'j} <--
   xterm_term{'i}; tok_sub; xterm_term{'j}

production xterm_term{'i *@ 'j} <--
   xterm_term{'i}; tok_mul; xterm_term{'j}

production xterm_term{'i /@ 'j} <--
   xterm_term{'i}; tok_div; xterm_term{'j}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
