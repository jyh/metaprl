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
extends Meta_extensions_theory
extends Itt_theory

doc docoff

open Basic_tactics

declare Invalid_argument

(************************************************************************
 * Simple version.
 *)
doc <:doc<
   The bind terms are modeled after the terms in Itt_hoas_base.
   The function space is marked by a disjoint union.
>>
define unfold_mk_bind : mk_bind{x. 'e['x]} <-->
   inl{lambda{x. 'e['x]}}

define unfold_mk_core : mk_core{'e} <-->
   inr{'e}

define unfold_dest_bind : dest_bind{'e; 'bind; t. 'core['t]} <-->
   decide{'e; x. 'bind; y. 'core['y]}

define unfold_bind_subst : bind_subst{'e1; 'e2} <-->
   decide{'e1; f. 'f 'e2; x. "Invalid_argument"}

doc <:doc<
   Rewriting for the << dest_bind{'e; 'bind; t. 'core['t]} >> term.
>>
interactive_rw reduce_dest_bind_bind {| reduce |} :
   dest_bind{mk_bind{x. 'e1['x]}; 'base; t. 'core['t]}
   <-->
   'base

interactive_rw reduce_dest_bind_core {| reduce |} :
   dest_bind{mk_core{'e1}; 'base; t. 'core['t]}
   <-->
   'core['e1]

interactive_rw reduce_subst_bind {| reduce |} :
   bind_subst{mk_bind{x. 'e1['x]}; 'e2}
   <-->
   'e1['e2]

(************************************************************************
 * Vector version.
 *)
doc <:doc<
   A vector binding ignores the actual hyp values and just performs a bind
   of the comclusion.
>>
prim_rw unfold_mk_vbind : <:xrewrite<
   "mk_vbind"{| <J> >- C |}
   <-->
   sequent_ind{u, v. mk_bind{x. happly{v; x}}; "TermSequent"{| <J> >- C |}}
>>

doc <:doc<
   Reductions.
>>
interactive_rw reduce_mk_vbind_nil {| reduce |} : <:xrewrite<
   "mk_vbind"{| >- C |}
   <-->
   C
>>

interactive_rw reduce_mk_vbind_left {| reduce |} : <:xrewrite<
   "mk_vbind"{| x: A; <J[x]> >- C[x] |}
   <-->
   mk_bind{x. "mk_vbind"{| <J[x]> >- C[x] |}}
>>

interactive_rw reduce_mk_vbind_right {| reduce |} : <:xrewrite<
   "mk_vbind"{| <J>; x: A >- C[x] |}
   <-->
   "mk_vbind"{| <J> >- mk_bind{x. C[x]} |}
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
