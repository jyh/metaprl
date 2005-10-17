doc <:doc<
   @module[Itt_hoas_lang]
   The @tt[Itt_hoas_lang] module defines the type of a language over
   a list of operators.

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

   Authors: Xin Yu @email{xiny@cs.caltech.edu}

   @end[license]
>>
extends Itt_hoas_destterm

open Tactic_type.Tactic

define iform unfold_SubOp : SubOp{'ops} <--> listmem_set{'ops; Operator}

declare compatible_shapes{'bdepth;'op;'subterms}
declare dom{'sop; 'BT}
declare mk{'x}
declare dest{'bt}
declare Iter{'sop; 'X}
declare BT{'sop; 'n}
declare Lang{'ops}
define iform unfold_BTerm: BTerm <--> Lang{Operator}


topval unfold_compatible_shapes : conv
topval unfold_Ldom : conv
topval unfold_mk : conv
topval unfold_dest : conv
topval unfold_LIter : conv
topval unfold_LBT : conv
topval unfold_Lang : conv
topval fold_Ldom : conv
topval fold_mk : conv
topval fold_LIter : conv
topval fold_dest : conv
topval fold_Lang : conv
topval fold_ndepth : conv

(************************************************************************
 * Grammar.
 *)
declare tok_Lang       : Terminal

lex_token itt : "Lang"     --> tok_Lang

lex_prec right [tok_Lang]       = prec_not

production itt_term{Lang{listmem_set{'ops; Operator}}} <--
   tok_Lang; itt_term{'ops}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
