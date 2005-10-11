doc <:doc<
   @module[Itt_hoas_debruijn]
   The @tt[Itt_hoas_debruijn] module defines a mapping from de Bruijn-like
   representation of syntax into the HOAS.

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
extends Itt_nat
extends Itt_list2

declare var{'left; 'right}
declare mk_bterm{'n; 'op; 'btl}
declare bdepth{'bt}
declare left{'v}
declare right{'v}
declare get_op{'bt; 'op}
declare subterms{'bt}
declare not_found
define iform unfold_get_op1:
   get_op{'bt} <--> get_op{'bt; not_found}

(************************************************************************
 * Grammar.
 *)
declare tok_bterm     : Terminal

lex_token itt : "bterm"     --> tok_bterm

lex_prec right [tok_bterm] = prec_let

production itt_term{var{'left; 'right}} <--
   tok_tilde; tok_lt; itt_term{'left}; tok_semi; itt_term{'right}; tok_gt

production itt_term{mk_bterm{'n; 'op; 'btl}} <--
   tok_bterm; itt_apply_term{'n}; tok_arrow; itt_term{'op}; tok_hash; itt_term{'btl}

(*
 * Various projections.
 *)
iform unfold_depth :
    parsed_proj["depth"]{'t}
    <-->
    bdepth{'t}

iform unfold_left :
    parsed_proj["left"]{'t}
    <-->
    left{'t}

iform unfold_right :
    parsed_proj["right"]{'t}
    <-->
    right{'t}

iform unfold_get_op :
    parsed_proj["op"]{'t}
    <-->
    get_op{'t}

iform unfold_subterms :
    parsed_proj["subterms"]{'t}
    <-->
    subterms{'t}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
