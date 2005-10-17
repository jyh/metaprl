doc <:doc<
   @module[Itt_hoas_operator]
   The @tt[Itt_hoas_operator] module defines a type << Operator >> of abstract
   operators; it also estabishes the connection between abstract operator type
   and the internal notion of syntax that is exposed by the computational bterms
   theory (@hrefmodule[Base_operator]).

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

   Authors: Aleksey Nogin @email{nogin@cs.caltech.edu}
            Alexei Kopylov @email{kopylov@cs.caltech.edu}
            Xin Yu @email{xiny@cs.caltech.edu}

   @end[license]
>>

extends Itt_nat
extends Itt_list2

declare Operator
declare shape{'op}
declare is_same_op{'op_1;'op_2}

define iform unfold_arity : arity{'op} <--> length{shape{'op}}

(************************************************************************
 * Grammar.
 *)
(* JYH: This was not public, is it really supposed to be hidden? *)
declare operator[op:op]

declare tok_Lang       : Terminal
declare tok_Operator   : Terminal
declare tok_is_same_op : Terminal

lex_token itt : "Lang"     --> tok_Lang
lex_token itt : "Operator" --> tok_Operator
lex_token itt : "=\[op\]=" --> tok_is_same_op

lex_prec right [tok_is_same_op] = prec_equal
lex_prec right [tok_Lang]       = prec_not

production itt_simple_term{Operator} <--
   tok_Operator

production itt_term{is_same_op{'op1; 'op2}} <--
   itt_term{'op1}; tok_is_same_op; itt_term{'op2}

production itt_term{operator[t:op]} <--
   tok_hash; itt_term{'t}

production itt_term{listmem_set{'ops; Operator}} <--
   tok_Lang; itt_term{'ops}

iform unfold_shape :
   parsed_proj["shape"]{'t}
   <-->
   shape{'t}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
