doc <:doc<
   @spelling{thinned thins}
   @module[Itt_vec_struct]

   The @tt[Itt_vec_struct] module defines @emph{structural} rules
   for context variables.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998-2005 MetaPRL Group, Caltech

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}

   @end[license]

   @parents
>>
extends Itt_struct
extends Meta_extensions_theory
doc docoff

open Basic_tactics

interactive context_thin 'H 'J :
   sequent { <H>; <K> >- 'C } -->
   sequent { <H>; <J<||> >; <K<|H|> > >- 'C<|H;K|> }

interactive exchange 'H :
   sequent { <H>; y: 'A2; x: 'A1; <J['x; 'y]> >- 'C['x; 'y] } -->
   sequent { <H>; x: 'A1; y: 'A2; <J['x; 'y]> >- 'C['x; 'y] }

interactive context_exchange_lemma 'H 'J :
   sequent { <H>; <J>; x: 'A; <K['x]> >- 'C['x] } -->
   sequent { <H>; x: 'A; <J>; <K['x]> >- 'C['x] }

interactive context_exchange 'H 'J 'K :
   sequent { <H>; <K>; <J>; <L> >- 'C } -->
   sequent { <H>; <J>; <K<|H|> >; <L> >- 'C }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
