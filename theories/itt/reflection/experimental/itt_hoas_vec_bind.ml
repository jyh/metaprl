doc <:doc<
   @module[Itt_hoas_vec_bind]

   Vector binder.

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
extends Itt_vec_theory
extends Itt_hoas_base

doc docoff

open Basic_tactics

doc <:doc<
   A vector binding ignores the actual hyp values and just performs a bind
   of the comclusion.
>>
prim_rw unfold_vbind : <:xrewrite<
   "vbind"{| <J> >- C |}
   <-->
   sequent_ind{u, v. bind{x. happly{v; x}}; "TermSequent"{| <J> >- C |}}
>>

doc <:doc<
   Reductions.
>>
interactive_rw reduce_vbind_nil {| reduce |} : <:xrewrite<
   "vbind"{| >- C |}
   <-->
   C
>>

interactive_rw reduce_vbind_left {| reduce |} : <:xrewrite<
   "vbind"{| x: A; <J[x]> >- C[x] |}
   <-->
   bind{x. "vbind"{| <J[x]> >- C[x] |}}
>>

interactive_rw reduce_vbind_right {| reduce |} : <:xrewrite<
   "vbind"{| <J>; x: A >- C[x] |}
   <-->
   "vbind"{| <J> >- bind{x. C[x]} |}
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
