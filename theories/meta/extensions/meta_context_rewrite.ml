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
   There is a corresponding reduction rule on the right.
>>
interactive_rw reduce_sequent_ind_right {| reduce |} :
   sequent_ind{h. 'step['h]; Sequent{| <J>; x: 'A >- 'C['x] |}}
   <-->
   sequent_ind{h. 'step['h]; Sequent{| <J> >- 'step[hlambda{'A; x. 'C['x]}] |}}

doc <:doc<
   Define a spread version of sequent induction.
>>
define unfold_sequent_ind_uv :
   sequent_ind{u : 'b, v : HFun{'a; 'b; 'c}. 'step['u; 'v] : 'c; 'e : SequentCore{'a; 'b; 'c}} : 'c
   <-->
   sequent_ind{h. 'step[htype{'h}; 'h]; 'e}

interactive_rw reduce_sequent_ind_nil2 {| reduce |} :
   sequent_ind{u, v. 'step['u; 'v]; Sequent{| >- 'C |}}
   <-->
   'C

interactive_rw reduce_sequent_ind_left2 {| reduce |} :
   sequent_ind{u, v. 'step['u; 'v]; Sequent{| x: 'A; <H['x]> >- 'C['x] |}}
   <-->
   'step['A; hlambda{'A; x. sequent_ind{u, v. 'step['u; 'v]; Sequent{| <H['x]> >- 'C['x] |}}}]

interactive_rw reduce_sequent_ind_right2 {| reduce |} :
   sequent_ind{u, v. 'step['u; 'v]; Sequent{| <H>; x: 'A >- 'C['x] |}}
   <-->
   sequent_ind{u, v. 'step['u; 'v]; Sequent{| <H> >- 'step['A; hlambda{'A; x. 'C['x]}] |}}

doc <:doc<
   Define a complete version of sequent induction.
>>
define unfold_sequent_ind_cuv :
   sequent_ind{x : 'c. 'concl['x] : 'result;
               u : 'b, v : HFun{'a; 'b; 'result}. 'step['u; 'v] : 'result;
               'e : SequentCore{'a; 'b; 'c}} : 'result
   <-->
   sequent_ind{y, x. 'concl['x]; h. 'step[htype{'h}; 'h]; 'e}

interactive_rw reduce_sequent_ind_nil3 {| reduce |} :
   sequent_ind{x. 'c['x]; u, v. 'step['u; 'v]; Sequent{| <J> >- 'C |}}
   <-->
   sequent_ind{u, v. 'step['u; 'v]; Sequent{| <J> >- 'c['C] |}}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
