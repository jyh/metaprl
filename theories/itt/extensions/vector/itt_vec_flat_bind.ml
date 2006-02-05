doc <:doc<
   @module[Itt_vec_bind]

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
extends Meta_context_theory
extends Itt_vec_bind

doc docoff

open Basic_tactics

(************************************************************************
 * Definitions.
 *)
doc <:doc<
   Vector binder.
>>
define unfold_mk_bindn : mk_bind{'n; x. 'e['x]} <--> <:xterm<
   ind{n; lambda{f. f ([])}; _, r. lambda{f. mk_bind{v. r (lambda{l. f (v :: l)})}}} lambda{x. e[x]}
>>

define unfold_bind_substl : bind_substl{'e; 'l} <--> <:xterm<
   list_ind{l; lambda{e. e}; u, _, g. lambda{e. g bind_subst{e; u}}} l
>>

doc <:doc<
   Binder that is defined by arity.
>>
prim_rw unfold_mk_flat_vbind : <:xrewrite<
   mk_flat_vbind{| <J> >- C |}
   <-->
   sequent_ind{u, v. mk_bind{length{u}; x. happly{v; x}}; TermSequent{| <J> >- C |}}
>>

(************************************************************************
 * Simple rewrites.
 *)
doc <:doc<
   Simple reductions.
>>
interactive_rw reduce_mk_bindn_zero {| reduce |} : <:xrewrite<
   mk_bind{0; x. e[x]}
   <-->
   e[ [] ]
>>

interactive_rw reduce_mk_bindn_succ {| reduce |} : <:xrewrite<
   n in nat -->
   mk_bind{n +@ 1; x. e[x]}
   <-->
   mk_bind{x. mk_bind{n; y. e[x::y]}}
>>

interactive_rw reduce_mk_flat_vbind_nil {| reduce |} : <:xrewrite<
   mk_flat_vbind{| >- C |}
   <-->
   C
>>

interactive_rw reduce_mk_flat_vbind_left : <:xrewrite<
   mk_flat_vbind{| x: A; <J[x]> >- C[x] |}
   <-->
   mk_bind{length{A}; x. mk_flat_vbind{| <J[x]> >- C[x] |}}
>>

(************************************************************************
 * Tactics.
 *)
doc docoff

let fold_mk_bindn = makeFoldC <:xterm< mk_bind{n; x. e[x]} >> unfold_mk_bindn

(*
 * -*-
 * Local Variables:
 * Fill-column: 120
 * End:
 * -*-
 * vim:ts=3:et:tw=120
 *)
