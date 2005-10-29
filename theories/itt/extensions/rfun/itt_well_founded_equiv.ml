doc <:doc<
   @module[Itt_well_founded]

   The @tt{Itt_well_founded} module provides a more convenient
   description of well-foundness than the @hrefterm[well_founded_prop]
   term formalized in the @hrefmodule[Itt_rfun] module.  The definition
   of well-foundness requires the derivation of an induction
   principle.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1999 Jason Hickey, Cornell University

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

   Author: Jason Hickey
   @email{jyh@cs.cornell.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_rfun
extends Itt_well_founded
extends Itt_dfun
extends Itt_logic

doc <:doc<
   The purpose of this definition is to give a more convenient
   specification of well-foundness that uses normal quantification
   in its formalization (the @hrefterm[well_founded_prop] predicate defined
   in the @hrefmodule[Itt_rfun] can't use the function type in its
   definition).  The following rule specifies that the new
   description of well-foundness is sufficient to derive the
   primitive definition.
>>
interactive well_founded_reduction univ[i:l] :
   [wf] sequent { <H> >- 'A in univ[i:l] } -->
   [wf] sequent { <H>; a: 'A; b: 'A >- 'R['a; 'b] in univ[i:l] } -->
   [main] sequent { <H> >- well_founded[i:l]{'A; x, y. 'R['x; 'y]} } -->
   sequent { <H> >- Itt_rfun!well_founded{'A; x, y. 'R['x; 'y]} }

doc docoff

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
