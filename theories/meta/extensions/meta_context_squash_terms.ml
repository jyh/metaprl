doc <:doc<
   @module["meta_context_simple"]

   Simplified form of context induction where the hypotheses are squashed.

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Meta_context_terms
extends Meta_context_ind1
extends Meta_rewrite

doc docoff

open Basic_tactics

doc <:doc<
   This is a limited form of context induction, where the hypotheses dependencies
   are squashed.
>>
prim_rw reduce_squash_sequent_ind_base2 {| reduce |} :
   squash_sequent_ind{h. 'step['h]; SequentTerm{| >- 'C |}}
   <-->
   'C

prim_rw reduce_squash_sequent_ind_left {| reduce |} :
   squash_sequent_ind{h. 'step['h]; SequentTerm{| x: 'A; <H['x]> >- 'C['x] |}}
   <-->
   'step[hlambda{'A; x. squash_sequent_ind{h. 'step['h]; SequentTerm{| <H[it]> >- 'C['x] |}}}]

(*
 * JYH: the right rules are not derivable I believe.
 * They are also very weak.
interactive_rw reduce_squash_sequent_ind_right {| reduce |} :
   squash_sequent_ind{h. 'step['h]; SequentTerm{| <J>; x: 'A<||> >- 'C['x] |}}
   <-->
   squash_sequent_ind{h. 'step['h]; SequentTerm{| <J> >- 'step[hlambda{'A; x. 'C['x]}] |}}
 *)

define unfold_squash_sequent_ind_uv :
   squash_sequent_ind{u : 'b, v : HFun{Term; 'b; 'c}. 'step['u; 'v] : 'c; 'e : Sequent{Term; 'b; 'c}} : 'c
   <-->
   squash_sequent_ind{h. 'step[htype{'h}; 'h]; 'e}

interactive_rw reduce_squash_sequent_ind_uv_base {| reduce |} :
   squash_sequent_ind{u, v. 'step['u; 'v]; SequentTerm{| >- 'C |}}
   <-->
   'C

interactive_rw reduce_squash_sequent_ind_uv_left {| reduce |} :
   squash_sequent_ind{u, v. 'step['u; 'v]; SequentTerm{| x: 'A; <H['x]> >- 'C['x] |}}
   <-->
   'step['A; hlambda{'A; x. squash_sequent_ind{u, v. 'step['u; 'v]; SequentTerm{| <H[it]> >- 'C['x] |}}}]

(*
interactive_rw reduce_squash_sequent_ind_uv_right {| reduce |} :
   squash_sequent_ind{u, v. 'step['u; 'v]; SequentTerm{| <H>; x: 'A<||> >- 'C['x] |}}
   <-->
   squash_sequent_ind{u, v. 'step['u; 'v]; SequentTerm{| <H> >- 'step['A; hlambda{'A; x. 'C['x]}] |}}
 *)

(*
 * -*-
 * Local Variables:
 * Fill-column: 120
 * End:
 * -*-
 * vim:ts=3:et:tw=120
 *)
