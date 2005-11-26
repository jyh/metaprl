(*
 * Derived rewrites.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends Meta_rewrite
extends Meta_context_ind1

doc docoff

open Basic_tactics
open Meta_rewrite
open Meta_context_terms

doc <:doc<
   Two functions are equal if their bodies are equal.
>>
interactive hlambda_equal bind{x. 'e1['x]} bind{x. 'e2['x]} :
   sequent { <H> >- rewrite_context{| <J>; x: 'A >- Perv!"rewrite"{'e1['x]; 'e2['x]} |} } -->
   sequent { <H> >- rewrite_context{| <J> >- Perv!"rewrite"{hlambda{'A; x. 'e1['x]}; hlambda{'A; x. 'e2['x]}} |} }

doc docoff

let hlambda_rw p =
   let t = Sequent.concl p in
   let _, t = dest_rewrite_context_term t in
   let t1, t2 = dest_rewrite_term t in
   let x1, _, t1 = dest_hlambda_term t1 in
   let x2, _, t2 = dest_hlambda_term t2 in
   let t1 = mk_bind1_term x1 t1 in
   let t2 = mk_bind1_term x2 t2 in
      hlambda_equal t1 t2

let hlambda_rw = funT hlambda_rw

open Basic_tactics

interactive_rw reduce_sequent_ind_right {| reduce |} :
   sequent_ind{h. 'step['h]; Sequent{| <J>; x: 'A >- 'C['x] |}}
   <-->
   sequent_ind{h. 'step['h]; Sequent{| <J> >- 'step[hlambda{'A; x. 'C['x]}] |}}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
