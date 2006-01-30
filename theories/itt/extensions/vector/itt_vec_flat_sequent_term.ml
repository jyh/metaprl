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
extends Meta_context_theory
extends Itt_vec_sequent_term
extends Itt_vec_flat_bind
extends Itt_vec_list1

doc docoff

open Basic_tactics

doc <:doc<
   The items in the hypothesis list are lists.
>>
define unfold_mk_core_list : mk_core_list{'l} <--> <:xterm<
   map{x. mk_core{x}; l}
>>

define unfold_mk_it_vec : mk_it_vec{'n} <--> <:xterm<
   ind{n; []; i, g. it::g}
>>

doc <:doc<
   The hypothesis list is constructed by sequent induction,
   flattening the list on each step.  This algorithm is quadratic,
   but since we only use it for computing representations, it
   doesn't matter.
>>
declare sequent [flat_hypconslist] { Term : Term >- Term } : Term

prim_rw unfold_flat_hypconslist : <:xrewrite<
   flat_hypconslist{| <J> >- C |}
   <-->
   sequent_ind{u, v. append{mk_core_list{u}; hyps_flatten{mk_bind{length{u}; x. mk_core{happly{v; x}}}}}; "TermSequent"{| <J> >- C |}}
>>

declare sequent [flat_hyplist] { Term : Term >- Term } : Term

prim_rw unfold_flat_hyplist : <:xrewrite<
   flat_hyplist{| <J> >- C |}
   <-->
   flat_hypconslist{| <J> >- [] |}
>>

doc <:doc<
   The @tt[flat_sequent] is a small variation, where the hyps are lists,
   not terms.  The actual sequent is based on the flattened form.
>>
prim_rw unfold_flat_sequent : <:xrewrite<
   flat_sequent{arg}{| <J> >- C |}
   <-->
   (arg, flat_hyplist{| <J> |}, mk_flat_vbind{| <J> >- mk_core{C} |})
>>

(************************************************************************
 * Simple reductions.
 *)
doc docoff

interactive_rw reduce_mk_it_vec_zero {| reduce |} : <:xrewrite<
   mk_it_vec{0}
   <-->
   []
>>

interactive_rw reduce_mk_it_vec_succ {| reduce |} : <:xrewrite<
   n in nat -->
   mk_it_vec{n +@ 1}
   <-->
   it :: mk_it_vec{n}
>>

interactive_rw reduce_hyps_length_bind {| reduce |} : <:xrewrite<
   n in nat -->
   hyps_length{mk_bind{n; x. e[x]}}
   <-->
   hyps_length{e[mk_it_vec{n}]}
>>

interactive_rw reduce_hyps_nth_bind {| reduce |} : <:xrewrite<
   n in nat -->
   hyps_nth{mk_bind{n; x. e[x]}; i}
   <-->
   mk_bind{n; x. hyps_nth{e[x]; i}}
>>

(************************************************************************
 * Flat bind reductions.
 *)
interactive_rw reduce_hyps_length_bind_null : <:xrewrite<
   vlist{| <J> |} in list{list} -->
   hyps_length{mk_flat_vbind{| <J> >- e<||> |}}
   <-->
   hyps_length{e}
>>

(************************************************************************
 * Basic hypconslist reductions.
 *)
interactive_rw reduce_flat_hypconslist_concl {| reduce |} : <:xrewrite<
   flat_hypconslist{| >- C |}
   <-->
   C
>>

interactive_rw reduce_flat_hypconslist_left : <:xrewrite<
   flat_hypconslist{| x: A; <J[x]> >- C[x] |}
   <-->
   append{mk_core_list{'A}; hyps_flatten{mk_flat_vbind{| x : A >- mk_core{flat_hypconslist{| <J[x]> >- C[x] |}} |}}}
>>

interactive_rw reduce_flat_hypconslist_right : <:xrewrite<
   flat_hypconslist{| <J>; x: A >- C[x] |}
   <-->
   flat_hypconslist{| <J> >- append{mk_core_list{A}; hyps_flatten{mk_flat_vbind{| x: A >- mk_core{C[x]} |}}} |}
>>

interactive_rw reduce_flat_hypconslist_shift {| reduce |} : <:xrewrite<
   flat_hypconslist{| <J>; x: A >- flat_hypconslist{| <K[x]> >- C[x] |} |}
   <-->
   flat_hypconslist{| <J> >- flat_hypconslist{| x: A; <K[x]> >- C[x] |} |}
>>

interactive_rw reduce_flat_hypconslist_merge : <:xrewrite<
   flat_hypconslist{| <J> >- flat_hypconslist{| <K> >- [] |} |}
   <-->
   flat_hypconslist{| <J>; <K> >- [] |}
>>

(************************************************************************
 * Well-formedness.
 *)
interactive hyps_length_flat_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- e in list -->
   "wf" : <H> >- vlist{| <J> |} in list{list} -->
   <H> >- hyps_length{mk_flat_vbind{| <J> >- mk_core{e<|H|>} |}} in nat
>>

interactive flat_hypconslist_is_list {| intro [] |} : <:xrule<
   "wf" : <H> >- vlist{| <J> |} in list{list} -->
   <H> >- flat_hypconslist{| <J> >- [] |} in list
>>

interactive flat_hypconslist_is_list2 {| intro [] |} : <:xrule<
   "wf" : <H> >- l in list -->
   "wf" : <H> >- vlist{| <J> |} in list{list} -->
   <H> >- flat_hypconslist{| <J> >- l<|H|> |} in list
>>

interactive flat_hypconslist_is_list3 {| intro [] |} : <:xrewrite<
   "wf" : <H> >- vlist{| <J>; <K> |} in list{list} -->
   <H> >- flat_hypconslist{| <J> >- flat_hypconslist{| <K> >- [] |} |} in list
>>

interactive hyps_length_flat_bind_hypconslist_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l in list -->
   "wf" : <H> >- vlist{| <J>; <K> |} in list{list} -->
   <H> >- hyps_length{mk_flat_vbind{| <J> >- mk_core{flat_hypconslist{| <K> >- l<|H|> |}} |}} in nat
>>

interactive hyps_length_flat_bind_squashlist_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l in list -->
   "wf" : <H> >- vlist{| <J>; <K> |} in list{list} -->
   <H> >- hyps_length{mk_flat_vbind{| <J> >- mk_core{squashlist{| <K> >- l<|H|> |}} |}} in nat
>>

interactive hyps_flatten_flat_bind_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l in list -->
   "wf" : <H> >- vlist{| <J>; <K> |} in list{list} -->
   <H> >- hyps_flatten{mk_flat_vbind{| <J> >- mk_core{flat_hypconslist{| <K> >- l<||> |}} |}} in list
>>

(************************************************************************
 * Tactics.
 *)
let fold_flat_hypconslist = makeFoldC <:xterm< flat_hypconslist{| <J> >- C |} >> unfold_flat_hypconslist

(*
 * -*-
 * Local Variables:
 * Fill-column: 120
 * End:
 * -*-
 * vim:ts=3:et:tw=120
 *)
