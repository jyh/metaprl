doc <:doc<
   @module[Itt_hoas_destterm]
   The @tt[Itt_hoas_destterm] module defines destructors for extracting
   from a bterm the components corresponding to the de Bruijn-like representation
   of that bterm.

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
extends Itt_hoas_base
extends Itt_hoas_vector
extends Itt_hoas_operator
extends Itt_hoas_debruijn

declare is_var{'bt}
declare dest_bterm{'bt; l, r. 'var_case['l; 'r]; bdepth, op, subterms. 'op_case['bdepth,'op; 'subterms] }

(************************************************************************
 * Grammar.
 *)
declare tok_dest_bterm  : Terminal

lex_token xterm : "dest_bterm" --> tok_dest_bterm

lex_prec left  [tok_dest_bterm] = prec_let

production xterm_term{dest_bterm{'t; l, r. 'var_case; bdepth, op, subterms. 'op_case}} <--
   tok_dest_bterm; xterm_term{'t}; tok_with;
   opt_pipe; tok_id[l:s]; tok_comma; tok_id[r:s]; tok_arrow; xterm_term{'var_case};
   tok_pipe; tok_id[bdepth:s]; tok_comma; tok_id[op:s]; tok_comma; tok_id[subterms:s]; tok_arrow; xterm_term{'op_case}

(*
 * Define a grammar of reflected terms.
 *)
declare tok_quote_term   : Terminal
declare tok_mquote_term  : Terminal
declare tok_unquote_term : Terminal

lex_token xterm : "[$]`"  --> tok_quote_term
lex_token xterm : "[$],"  --> tok_unquote_term
lex_token xterm : "[$]#"  --> tok_mquote_term

lex_prec nonassoc [tok_quote_term; tok_mquote_term; tok_unquote_term] = prec_not

production xterm_term{xquote{'depth; 't}} <--
   tok_quote_term; tok_left_brack; xterm_term{'depth}; tok_right_brack; xterm_term{'t}

production xterm_term{xquote{'t}} <--
   tok_quote_term; xterm_simple_term{'t}

production xterm_term{xmquote{'t}} <--
   tok_mquote_term; xterm_simple_term{'t}

production xterm_term{xunquote{'t}} <--
   tok_unquote_term; xterm_term{'t}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
