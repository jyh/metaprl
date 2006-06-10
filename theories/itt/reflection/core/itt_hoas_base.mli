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
extends Itt_list2

open Basic_tactics

declare bind{x. 't['x]}
declare mk_term{'op; 'subterms}
declare subst{'bt; 't}

define iform bind_list: bind_list{'terms} <--> map{bt. bind{x.'bt}; 'terms}
define iform subst_list: subst_list{'terms;'v} <-->  map{bt. subst{'bt; 'v}; 'terms}

declare weak_dest_bterm{'bt; 'bind_case; op, sbt. 'subterms_case['op; 'sbt]}

(* This is useful for working with subterm lists *)
declare mk_terms{'terms}
declare weak_dest_terms{'bt; 'bind_case; terms. 'terms_case['terms]}

(************************************************************************
 * Grammar for destructor.
 *)
declare tok_weak_dest_bterm : Terminal

lex_token xterm : "weak_dest_bterm" --> tok_weak_dest_bterm

lex_prec right [tok_weak_dest_bterm] = prec_let

production xterm_term{weak_dest_bterm{'bt; 'base; op, subterms. 'step}} %prec prec_let <--
   tok_weak_dest_bterm; xterm_term{'bt}; tok_with;
   opt_pipe; tok_arrow; xterm_term{'base};
   tok_pipe; tok_id[op:s]; tok_comma; tok_id[subterms:s]; tok_arrow; xterm_term{'step}

(************************************************************************
 * Tactics.
 *)
val is_bind_term : term -> bool
val mk_bind_term : var -> term -> term
val dest_bind_term : term -> var * term

val is_mk_term_term : term -> bool
val mk_mk_term_term : term -> term -> term
val dest_mk_term_term : term -> term * term

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
