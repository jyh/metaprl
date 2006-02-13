doc <:doc<
   @module[Itt_image]

   The @tt{Itt_image} adds a new type constructor <<Img{'A, x.'f['x]}>> with ther
   following semantics:

   If $A$ is a type with a PER $P_a$, then <<Img{'A, x.'f['x]}>> is a type with the
   the PER Transitive closure$(<<('f['a]='f['b] in Img{'A, x.'f['x]) <=> ('a='b in 'A)>>)$

   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2005 MetaPRL Group

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

   Author: Aleksey Nogin
   @email{nogin@cs.caltech.edu}

   @end[license]
>>

doc <:doc< @parents >>
extends Base_theory
extends Itt_equal
extends Itt_squash
extends Itt_struct2
extends Itt_sqsimple

doc terms

declare Img{'A; x.'f['x]}

open Basic_tactics

val dest_img_term : term -> var * term * term
