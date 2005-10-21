(*
 * Standard logical connectives.
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
extends Itt_rfun
extends Itt_dfun
extends Itt_dprod
extends Itt_prod
extends Itt_union
extends Itt_void
extends Itt_unit
extends Itt_struct

open Basic_tactics

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

define unfold_true : "true" <--> unit
define unfold_false : "false" <--> void

define unfold_not : "not"{'a} <--> 'a -> void

define unfold_and : "and"{'a; 'b} <--> 'a * 'b
define unfold_or : "or"{'a; 'b} <--> 'a + 'b
define unfold_implies : "implies"{'a; 'b} <--> 'a -> 'b
define unfold_iff : "iff"{'a; 'b} <--> (('a -> 'b) & ('b -> 'a))
define unfold_cand : "cand"{'a; 'b} <--> "and"{'a; 'b}
define unfold_cor : "cor"{'a; 'b} <--> "or"{'a; "cand"{"not"{'a}; 'b}}

define unfold_all : "all"{'A; x. 'B['x]} <--> x: 'A -> 'B['x]
define unfold_exists : "exists"{'A; x. 'B['x]} <--> x: 'A * 'B['x]

topval fold_true : conv
topval fold_false : conv
topval fold_not : conv
topval fold_implies : conv
topval fold_iff : conv
topval fold_and : conv
topval fold_or : conv
topval fold_cand : conv
topval fold_cor : conv
topval fold_all : conv
topval fold_exists : conv

(************************************************************************
 * DISPLAY FORMS							*
 ************************************************************************)

prec prec_iff
prec prec_implies
prec prec_and
prec prec_or
prec prec_not
prec prec_quant

(************************************************************************
 * RULES, used by other theories directly                               *
 ************************************************************************)

rule not_intro :
   [wf] sequent { <H> >- "type"{'t} } -->
   [main] sequent { <H>; x: 't >- "false" } -->
   sequent { <H> >- "not"{'t} }

rule not_elim 'H :
   [main] sequent { <H>; x: "not"{'t}; <J['x]> >- 't } -->
   sequent { <H>; x: "not"{'t}; <J['x]> >- 'C }

rule exists_elim 'H :
   [main] sequent { <H>; v: 'a; z: 'b['v]; <J['v, 'z]> >- 'C['v, 'z] } -->
   sequent { <H>; x: exst v: 'a. 'b['v]; <J['x]> >- 'C['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_false_term : term -> bool

val is_all_term : term -> bool
val dest_all : term -> var * term * term
val mk_all_term : var -> term -> term -> term

val is_exists_term : term -> bool
val dest_exists : term -> var * term * term
val mk_exists_term : var -> term -> term -> term

val is_or_term : term -> bool
val dest_or : term -> term * term
val mk_or_term : term -> term -> term

val is_and_term : term -> bool
val dest_and : term -> term * term
val mk_and_term : term -> term -> term

val is_cor_term : term -> bool
val dest_cor : term -> term * term
val mk_cor_term : term -> term -> term

val is_cand_term : term -> bool
val dest_cand : term -> term * term
val mk_cand_term : term -> term -> term

val is_implies_term : term -> bool
val dest_implies : term -> term * term
val mk_implies_term : term -> term -> term

val is_iff_term : term -> bool
val dest_iff : term -> term * term
val mk_iff_term : term -> term -> term

val is_not_term : term -> bool
val dest_not : term -> term
val mk_not_term : term -> term

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

topval univCDT : tactic
topval genUnivCDT : tactic
topval instHypT : term list -> int -> tactic

val logic_prec : auto_prec

topval backThruHypT : int -> tactic
topval assumT : int -> tactic
topval backThruAssumT : int -> tactic

topval moveToConclT : int -> tactic

topval genAssumT : int list -> tactic

(* JProver for itt_logic *)
topval jproverT : tactic
topval simple_jproverT : tactic (* JProver with max multiplicity 1; used by autoT *)

(* specifies maximal multiplicity for JProver *)
topval jAutoT : int -> tactic

(* Tries various backThruHyp and backThruAssum *)
topval logicAutoT : tactic

(************************************************************************
 * Grammar.
 *)
declare tok_not        : Terminal
declare tok_or         : Terminal
declare tok_and        : Terminal
declare tok_implies    : Terminal
declare tok_iff        : Terminal
declare tok_all        : Terminal
declare tok_exists     : Terminal

lex_token xterm : "not"       --> tok_not
lex_token xterm : "all"       --> tok_all
lex_token xterm : "exists"    --> tok_exists

lex_token xterm : "/"         --> tok_not
lex_token xterm : "[|][|]"    --> tok_or
lex_token xterm : "&&"        --> tok_and
lex_token xterm : "=>"        --> tok_implies
lex_token xterm : "<=>"       --> tok_iff

lex_prec right [tok_or] = prec_or
lex_prec right [tok_and] = prec_and
lex_prec right [tok_implies] = prec_implies
lex_prec right [tok_iff] = prec_iff
lex_prec right [tok_not] = prec_not

production xterm_term{not{'t}} <--
   tok_not; xterm_term{'t}

production xterm_term{'t1 or 't2} <--
   xterm_term{'t1}; tok_or; xterm_term{'t2}

production xterm_term{'t1 & 't2} <--
   xterm_term{'t1}; tok_and; xterm_term{'t2}

production xterm_term{'t1 => 't2} <--
   xterm_term{'t1}; tok_implies; xterm_term{'t2}

production xterm_term{'t1 <=> 't2} <--
   xterm_term{'t1}; tok_iff; xterm_term{'t2}

production xterm_term{all v: 't1. 't2} <--
   tok_all; tok_id[v:s]; tok_colon; xterm_term{'t1}; tok_dot; xterm_term{'t2}

production xterm_term{exst v: 't1. 't2} <--
   tok_exists; tok_id[v:s]; tok_colon; xterm_term{'t1}; tok_dot; xterm_term{'t2}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
