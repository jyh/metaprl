doc <:doc<
   @module[Itt_hoas_sequent_provable]

   Provability theorems in a sequent logic.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2005 Mojave Group, Caltech

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
   @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Itt_tunion
extends Itt_match
extends Itt_hoas_proof
extends Itt_hoas_sequent
extends Itt_hoas_sequent_term1
extends Itt_hoas_sequent_proof

doc docoff

open Basic_tactics

(************************************************************************
 * Defined terms.
 *)
define unfold_SeqProvable : SeqProvable{'logic; 'e} <-->
   Provable{Sequent; 'logic; 'e}

(************************************************************************
 * Provability.
 *)
interactive provable_intro : <:xrule<
   "wf" : <H> >- arg IN BTerm{0} -->
   "wf" : <H> >- "sequent_wf"{| <J> >- C |} -->
   <H>; A: CVar{0}; length{A} = bdepth{"vbind"{| <J> >- C |}} in "nat" >-
      SeqProvable{logic; "sequent"{arg; A; "vbind"{| <J> >- C |}}} -->
   <H> >- SeqProvable{logic; bsequent{arg}{| <J> >- C |}}
>>

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
