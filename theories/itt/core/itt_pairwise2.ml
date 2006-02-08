doc <:doc<
   @module[Itt_pointwise2]

   @parents
   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2004-2006 MetaPRL, California Institute of Technology

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

   Author: Alexei Kopylov @email{kopylov@cs.caltech.edu}
   @end[license]
>>

extends Itt_subtype
extends Itt_pairwise

doc docoff

open Basic_tactics

doc docon

interactive supertype 'H 'B:
   [wf] sequent  { <H>; x:'A; <J['x]> >- 'A subtype 'B} -->
   sequent  { <H>; x:'B; <J['x]> >- 'T['x]} -->
   sequent  { <H>; x:'A; <J['x]> >- 'T['x]}

doc docoff

let supertypeT b i =
   supertype i b

doc docon

interactive supertypeHyp 'H 'K:
   sequent  { <H>; 'A subtype 'B; <K>; x:'B; <J['x]> >- 'T['x]} -->
   sequent  { <H>; 'A subtype 'B; <K>; x:'A; <J['x]> >- 'T['x]}

