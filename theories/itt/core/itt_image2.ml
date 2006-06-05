doc <:doc<
   @module[Itt_image2]
   This module contains basic theorems about Image type.

   @docoff
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

extends Itt_image
extends Itt_sqsimple
extends Itt_squash
extends Itt_squiggle
extends Itt_dfun
extends Itt_pairwise
extends Itt_struct2
extends Itt_subset

open Basic_tactics
open Itt_struct

doc <:doc<
   When $f$ is squiggle-reversible, we can have elimination for non-squash-stable goals. Moreover,
   in this case we can derive a @emph{strong} version of the elimination rule.
>>

interactive img_elim2 {| elim [ThinOption thinT] |} 'H :
   sequent { <H>; y: Img{'A; a.'f<||>['a]}; <J['y]>; a: 'A >- squash{'C['f['a]]} } -->
   sequent { <H>; y: Img{'A; a.'f<||>['a]}; <J['y]> >- squash{'C['y]} }

interactive img_elim3 {| elim |} 'H 'g :
   [aux] sequent { <H>; y: Img{'A; a.'f<||>['a]}; <J['y]>; a: 'A >- 'g 'f['a] ~ 'a } -->
   sequent { <H>; a: 'A; <J['f['a]]> >- 'C['f['a]] } -->
   sequent { <H>; y: Img{'A; a.'f<||>['a]}; <J['y]> >- 'C['y] }

interactive img_sqsimple 'g :
   [aux] sequent { <H>; a: 'A >- 'g 'f['a] ~ 'a } -->
   sequent { <H> >- sqsimple{'A} } -->
   sequent { <H> >- sqsimple{Img{'A; x. 'f<||>['x]}} }

doc <:doc<
   The @tt[Image] operation is monotone on its first argument.
>>

interactive img_monotone {| intro[] |} :
   sequent { <H> >-  'A_1 subtype 'A_2 } -->
   sequent { <H> >-  Img{'A_1; x.'f<||>['x]} subtype  Img{'A_2; x.'f<||>['x]} }

interactive img_monotone_subset {| intro[] |} bind{x.'g['x]}:
   sequent { <H>; x:'A_2 >- 'g['f<||>['x]]='x in 'A_2 } -->
   sequent { <H> >-  'A_1 subset 'A_2 } -->
   sequent { <H> >-  Img{'A_1; x.'f<||>['x]} subset  Img{'A_2; x.'f<||>['x]} }

