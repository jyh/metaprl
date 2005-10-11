doc <:doc<
   @module[Itt_hoas_base]
   The @tt[Itt_hoas_base] module defines the basic operations of the
   Higher Order Abstract Syntax (HOAS).

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2005, MetaPRL Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>
extends Base_theory
extends Itt_grammar

declare bind{x. 't['x]}
declare mk_term{'op; 'subterms}
declare subst{'bt; 't}

declare weak_dest_bterm{'bt; 'bind_case; op, sbt. 'subterms_case['op; 'sbt]}

(************************************************************************
 * Grammar.
 *)
declare tok_bind       : Terminal
declare tok_quote      : Terminal
declare tok_match_term : Terminal

lex_token itt : "bind"   --> tok_bind
lex_token itt : "quote"  --> tok_quote
lex_token itt : "match_term" --> tok_match_term

lex_prec right [tok_bind; tok_quote; tok_match_term] = prec_let

(*
 * JYH: I'm not sure exactly what is an operator or subterm.
 *)
declare itt_operator{'op} : Nonterminal
declare itt_subterms{'t}  : Nonterminal

production itt_term{bind{x. 't}} <--
   tok_bind; tok_id[x:s]; tok_arrow; itt_term{'t}

production itt_term{mk_term{'op; 'subterms}} <--
   tok_quote; itt_operator{'op}; tok_left_curly; itt_subterms{'subterms}; tok_right_curly

production itt_term{subst{'bt; 't}} <--
   itt_term{'bt}; tok_at; itt_term{'t}

production itt_term{weak_dest_bterm{'bt; 'base; op, subterms. 'step}} %prec prec_let <--
   tok_match_term; itt_term{'bt}; tok_with;
   opt_pipe; tok_arrow; itt_term{'base};
   tok_pipe; tok_id[op:s]; tok_comma; tok_id[subterms:s]; tok_arrow; itt_term{'step}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
