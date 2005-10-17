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
declare dest_bterm{'bt; l,r.'var_case['l; 'r]; bdepth,op,subterms. 'op_case['bdepth,'op; 'subterms] }

(************************************************************************
 * Grammar.
 *)
declare tok_is_var      : Terminal
declare tok_match_term  : Terminal

lex_token itt : "is_var" --> tok_is_var
lex_token itt : "match_term" --> tok_match_term

lex_prec right [tok_is_var] = prec_apply
lex_prec left  [tok_match_term] = prec_let

production itt_term{is_var{'t}} <--
   tok_is_var; itt_term{'t}

production itt_term{dest_bterm{'t; l, r. 'var_case; bdepth, op, subterms. 'op_case}} <--
   tok_match_term; itt_term{'t}; tok_with;
   opt_pipe; tok_id[l:s]; tok_comma; tok_id[r:s]; tok_arrow; itt_term{'var_case};
   tok_pipe; tok_id[bdepth:s]; tok_comma; tok_id[op:s]; tok_comma; tok_id[subterms:s]; tok_arrow; itt_term{'op_case}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
