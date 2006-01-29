doc <:doc<
   Sequent flattening.

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
extends Itt_vec_sequent_term
extends Itt_vec_flat_bind

doc docoff

open Basic_tactics

doc <:doc<
   The @tt[flat_sequent] is a small variation, where the hyps are lists,
   not terms.  The actual sequent is based on the flattened form.
>>
prim_rw unfold_flat_sequent : <:xrewrite<
   flat_sequent{arg}{| <J> >- C |}
   <-->
   (arg, flat_hyplist{| <J> |}, mk_flat_vbind{| <J> >- mk_core{C} |})
>>

(*
 * -*-
 * Local Variables:
 * Fill-column: 120
 * End:
 * -*-
 * vim:ts=3:et:tw=120
 *)
