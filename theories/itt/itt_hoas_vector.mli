doc <:doc<
   The @tt[Itt_hoas_vector] module defines the ``vector bindings''
   extensions for the basic ITT HOAS.

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
extends Itt_nat
extends Itt_list2

declare bind{'n; x.'t['x]}
declare subst{'n; 'bt; 't}
declare substl{'bt; 'tl}

define iform simple_bindn: bind{'n; 't} <-->  bind{'n; x.'t}

(************************************************************************
 * Grammar.
 *)
declare tok_at_at : Terminal

lex_token itt : "@@" --> tok_at_at

lex_prec left [tok_at_at] = prec_apply

production itt_term{bind{'n; x. 't}} <--
   tok_bind; tok_id[x:s]; tok_colon; itt_simple_term{'n}; tok_arrow; itt_term{'t}

production itt_term{subst{'n; 'bt; 't}} <--
   itt_term{'bt}; tok_at; tok_left_curly; itt_term{'n}; tok_right_curly; itt_term{'t}

production itt_term{substl{'bt; 'tl}} <--
   itt_term{'bt}; tok_at_at; itt_term{'tl}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
