doc <:doc<
   @spelling{th}
   @module[Itt_list_set]

   The @tt{Itt_list_set} module defines a library of operations
   on lists that are interpreted as sets of elements.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998-2005 MetaPRL Group

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

   Author: Jason Hickey @email{jyh@cs.cornell.edu}
   Modified By: Aleksey Nogin @email{nogin@cs.cornell.edu}
   Modified By: Alexei Kopylov @email{kopylov@cs.cornell.edu}
   Modified By: Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
   @parents
>>
extends Itt_list2

doc docoff

open Basic_tactics

doc <:doc<
   The following theorems all have to do with lists-as-sets.
>>
interactive mem_append_left {| intro [SelectOption 1] |} :
   [wf] sequent { <H> >- 'x in 'ty } -->
   [wf] sequent { <H> >- 'l1 in list{'ty} } -->
   [wf] sequent { <H> >- 'l2 in list{'ty} } -->
   [wf] sequent { <H> >- mem{'x; 'l1; 'ty} } -->
   sequent { <H> >- mem{'x; append{'l1; 'l2}; 'ty} }

interactive mem_append_right {| intro [SelectOption 2] |} :
   [wf] sequent { <H> >- 'x in 'ty } -->
   [wf] sequent { <H> >- 'l1 in list{'ty} } -->
   [wf] sequent { <H> >- 'l2 in list{'ty} } -->
   [wf] sequent { <H> >- mem{'x; 'l2; 'ty} } -->
   sequent { <H> >- mem{'x; append{'l1; 'l2}; 'ty} }

doc <:doc<
   Subset membership.
>>
interactive subset_elim {| elim [] |} 'H 'x :
   [wf] sequent { <H>; \subset{'l1; 'l2; 'ty}; <J> >- 'ty Type } -->
   [wf] sequent { <H>; \subset{'l1; 'l2; 'ty}; <J> >- 'x in 'ty } -->
   [wf] sequent { <H>; \subset{'l1; 'l2; 'ty}; <J> >- 'l1 in list{'ty} } -->
   [wf] sequent { <H>; \subset{'l1; 'l2; 'ty}; <J> >- 'l2 in list{'ty} } -->
   [wf] sequent { <H>; \subset{'l1; 'l2; 'ty}; <J> >- mem{'x; 'l1; 'ty} } -->
   sequent { <H>; \subset{'l1; 'l2; 'ty}; <J>; mem{'x; 'l2; 'ty} >- 'C } -->
   sequent { <H>; \subset{'l1; 'l2; 'ty}; <J> >- 'C }

doc <:doc<
   Membership forms for the quantifiers.
>>
interactive exists_list_mem 'e 'ty :
   [wf] sequent { <H> >- 'ty Type } -->
   [wf] sequent { <H> >- 'e in 'ty } -->
   [wf] sequent { <H> >- 'l in list{'ty} } -->
   [wf] sequent { <H>; x: 'ty >- 'P['x] Type } -->
   sequent { <H> >- mem{'e; 'l; 'ty} } -->
   sequent { <H> >- 'P['e] } -->
   sequent { <H> >- exists_list{'l;  x. 'P['x]} }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
