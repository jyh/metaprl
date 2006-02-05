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
extends Itt_vec_list2
extends Itt_list3

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

interactive_rw reduce_mk_core_list_nil {| reduce |} : <:xrewrite<
   mk_core_list{[]}
   <-->
   []
>>

interactive_rw reduce_mk_core_list_cons {| reduce |} : <:xrewrite<
   mk_core_list{u::v}
   <-->
   mk_core{u}::mk_core_list{v}
>>

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
interactive hyps_flatten_list_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- hyps_length{e} in nat -->
   <H> >- hyps_flatten{e} in list
>>

interactive mk_core_list_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- A in list -->
   <H> >- mk_core_list{A} in list
>>

interactive hyps_length_flat_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- e in list -->
   "wf" : <H> >- vlistlistwf{| <J> |} -->
   <H> >- hyps_length{mk_flat_vbind{| <J> >- mk_core{e<|H|>} |}} in nat
>>

interactive flat_hypconslist_is_list {| intro [] |} : <:xrule<
   "wf" : <H> >- vlistlistwf{| <J> |} -->
   <H> >- flat_hypconslist{| <J> >- [] |} in list
>>

interactive flat_hypconslist_is_list2 {| intro [] |} : <:xrule<
   "wf" : <H> >- l in list -->
   "wf" : <H> >- vlistlistwf{| <J> |} -->
   <H> >- flat_hypconslist{| <J> >- l<|H|> |} in list
>>

interactive flat_hypconslist_is_list3 {| intro [] |} : <:xrewrite<
   "wf" : <H> >- vlistlistwf{| <J>; <K> |} -->
   <H> >- flat_hypconslist{| <J> >- flat_hypconslist{| <K> >- [] |} |} in list
>>

interactive hyps_length_flat_bind_hypconslist_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l in list -->
   "wf" : <H> >- vlistlistwf{| <J>; <K> |} -->
   <H> >- hyps_length{mk_flat_vbind{| <J> >- mk_core{flat_hypconslist{| <K> >- l<|H|> |}} |}} in nat
>>

interactive hyps_length_flat_bind_squashlist_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l in list -->
   "wf" : <H> >- vlistlistwf{| <J>; <K> |} -->
   <H> >- hyps_length{mk_flat_vbind{| <J> >- mk_core{squashlist{| <K> >- l<|H|> |}} |}} in nat
>>

interactive hyps_flatten_flat_bind_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l in list -->
   "wf" : <H> >- vlistlistwf{| <J>; <K> |} -->
   <H> >- hyps_flatten{mk_flat_vbind{| <J> >- mk_core{flat_hypconslist{| <K> >- l<||> |}} |}} in list
>>

(************************************************************************
 * Simple sq rules.
 *)
interactive plus_eq {| intro [] |} : <:xrule<
   "wf" : <H> >- i1 ~ i2 -->
   "wf" : <H> >- j1 ~ j2 -->
   <H> >- (i1 +@ j1) ~ (i2 +@ j2)
>>

interactive append_eq {| intro [] |} : <:xrule<
   "wf" : <H> >- i1 ~ i2 -->
   "wf" : <H> >- j1 ~ j2 -->
   <H> >- append{i1; j1} ~ append{i2; j2}
>>

(************************************************************************
 * List squashing.
 *)
define unfold_squashlist : squashlist{'l} <--> <:xterm<
   map{x. it; l}
>>

declare sequent [flat_squashlist] { Term : Term >- Term } : Term

prim_rw unfold_flat_squashlist : <:xrewrite<
   flat_squashlist{| <J> >- C |}
   <-->
   sequent_ind{u, v. append{squashlist{u}; happly{v; it}}; TermSequent{| <J> >- C |}}
>>

doc docoff

interactive_rw reduce_squashlist_nil {| reduce |} : <:xrewrite<
   squashlist{[]}
   <-->
   []
>>

interactive_rw reduce_squashlist_cons {| reduce |} : <:xrewrite<
   squashlist{x::l}
   <-->
   it::squashlist{l}
>>

interactive squashlist_wf {| intro [] |} : <:xrewrite<
   "wf" : <H> >- l in list -->
   <H> >- squashlist{l} in list
>>

interactive squashlist_wf2 {| intro [] |} : <:xrewrite<
   "wf" : <H> >- l in list -->
   <H> >- squashlist{l} in list{unit}
>>

interactive_rw reduce_flat_squashlist_concl {| reduce |} : <:xrewrite<
   flat_squashlist{| >- C |}
   <-->
   C
>>

interactive_rw reduce_flat_squashlist_left {| reduce |} : <:xrewrite<
   flat_squashlist{| x: A; <J[x]> >- C[x] |}
   <-->
   append{squashlist{A}; flat_squashlist{| <J[it]> >- C[it] |}}
>>

interactive_rw reduce_flat_squashlist_right {| reduce |} : <:xrewrite<
   flat_squashlist{| <J>; x: A >- C[x] |}
   <-->
   flat_squashlist{| <J> >- append{squashlist{A}; C[it]} |}
>>

interactive flat_squashlist_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l in list -->
   "wf" : <H> >- vlistlistwf{| <J> |} -->
   <H> >- flat_squashlist{| <J> >- l<|H|> |} in list
>>

interactive flat_squashlist_length_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l in list -->
   "wf" : <H> >- vlistlistwf{| <J> |} -->
   <H> >- length{flat_squashlist{| <J> >- l<|H|> |}} in nat
>>

interactive_rw reduce_flat_squashlist_append : <:xrewrite<
   vlistlistwf{| <J> |} -->
   flat_squashlist{| <J> >- l<||> |}
   <-->
   append{flat_squashlist{| <J> >- [] |}; l}
>>

interactive_rw reduce_flat_squashlist_squash <:xterm< bind{x. vlistlistwf{| <J[x]> |}} >> : <:xrewrite<
   l in list -->
   all x: top. vlistlistwf{| <J[x]> |} -->
   flat_squashlist{| <J[e]> >- l<||> |}
   <-->
   flat_squashlist{| <J[it]> >- l<||> |}
>>

(************************************************
 * Hyps length reductions.x
 *)
interactive_rw reduce_hyps_length_flat_squashlist : <:xrewrite<
   vlistlistwf{| <J> |} -->
   hyps_length{mk_core{flat_hypconslist{| <J> >- [] |}}}
   <-->
   length{flat_squashlist{| <J> >- [] |}}
>>

interactive_rw reduce_hyps_length_flat_squashlist_list {| reduce |} : <:xrewrite<
   l in list -->
   vlistlistwf{| <J> |} -->
   hyps_length{mk_core{flat_hypconslist{| <J> >- l<||> |}}}
   <-->
   length{flat_squashlist{| <J> >- l |}}
>>

interactive_rw reduce_hyps_length_bind_squashlist {| reduce |} : <:xrewrite<
   l in list -->
   vlistlistwf{| <J>; <K> |} -->
   hyps_length{mk_flat_vbind{| <J> >- mk_core{flat_hypconslist{| <K> >- l<||> |}} |}}
   <-->
   hyps_length{mk_flat_vbind{| <J> >- mk_core{flat_squashlist{| <K> >- l |}} |}}
>>

(************************************************************************
 * Reductions to append.
 *)
interactive_rw flat_nth_suffix_hypconslist {| reduce |} : <:xrewrite<
   i = length{flat_hypconslist{| <J> >- [] |}} in nat -->
   nth_suffix{flat_hypconslist{| <J> >- flat_hypconslist{| <K> >- [] |} |}; i}
   <-->
   hyps_flatten{mk_flat_vbind{| <J> >- mk_core{flat_hypconslist{| <K> >- [] |}} |}}
>>

(************************************************
 * Now the hoisting lemmas for occurrences
 * of << hyps_length{'e} >>.
 *)
interactive_rw flat_hyps_length_null : <:xrewrite<
   vlistlistwf{| <J> |} -->
   hyps_length{mk_flat_vbind{| <J> >- mk_core{l<||>} |}}
   <-->
   length{l}
>>

interactive_rw flat_hyps_length_bind_int 'i : <:xrewrite<
   vlistlistwf{| <J>; <K> |} -->
   i = hyps_length{mk_flat_vbind{| <J> >- mk_core{flat_hypconslist{| <K> >- [] |}} |}} in "nat" -->
   mk_flat_vbind{| <J> >- hyps_length{mk_core{flat_hypconslist{| <K> >- [] |}}} |}
   <-->
   mk_flat_vbind{| <J> >- i<||> |}
>>

interactive_rw flat_hoist_hyps_length 'i Perv!bind{x. 'S['x]} : <:xrewrite<
   i = hyps_length{mk_flat_vbind{| <J> >- mk_core{flat_hypconslist{| <K> >- [] |}} |}} in "nat" -->
   mk_flat_vbind{| <J> >- S[hyps_length{mk_core{flat_hypconslist{| <K> >- [] |}}}] |}
   <-->
   mk_flat_vbind{| <J> >- S[i<||>] |}
>>

interactive_rw flat_hyps_length_bind_int_vec 'i : <:xrewrite<
   i = hyps_length{mk_flat_vbind{| <J>; <K> >- mk_core{"squashlist"{| <L> >- [] |}} |}} in "nat" -->
   mk_flat_vbind{| <J> >- hyps_length{mk_flat_vbind{| <K> >- mk_core{"squashlist"{| <L> >- [] |}} |}} |}
   <-->
   mk_flat_vbind{| <J> >- i<||> |}
>>

interactive_rw flat_hoist_hyps_length_vec 'i Perv!bind{x. 'S['x]} : <:xrewrite<
   i = hyps_length{mk_flat_vbind{| <J>; <K> >- mk_core{"squashlist"{| <L> >- [] |}} |}} in "nat" -->
   mk_flat_vbind{| <J> >- S[hyps_length{mk_flat_vbind{| <K> >- mk_core{"squashlist"{| <L> >- [] |}} |}}] |}
   <-->
   mk_flat_vbind{| <J> >- S[i<||>] |}
>>

interactive_rw flat_reduce_hyps_nth_vec_bind {| reduce |} : <:xrewrite<
   mk_flat_vbind{| <J> >- hyps_nth{mk_flat_vbind{| <K> >- mk_core{flat_hypconslist{| <L> >- [] |}} |}; i<||>} |}
   <-->
   mk_flat_vbind{| <J>; <K> >- nth{flat_hypconslist{| <L> >- [] |}; i} |}
>>

interactive_rw flat_reduce_hyps_nth_vec_bind_tail {| reduce |} : <:xrewrite<
   hyps_nth{mk_flat_vbind{| <K> >- mk_core{flat_hypconslist{| <L> >- [] |}} |}; i<||>}
   <-->
   mk_flat_vbind{| <K> >- nth{flat_hypconslist{| <L> >- [] |}; i} |}
>>

interactive_rw flat_reduce_hyps_length_bind_right {| reduce |} : <:xrewrite<
   hyps_length{mk_flat_vbind{| <J>; x: A >- mk_core{"squashlist"{| <K[x]> >- [] |}} |}}
   <-->
   hyps_length{mk_flat_vbind{| <J> >- mk_core{"squashlist"{| <K["it"]> >- [] |}} |}}
>>

interactive_rw flat_reduce_hyps_length_bind_nil {| reduce |} : <:xrewrite<
   hyps_length{mk_flat_vbind{| <J> >- mk_core{[]} |}}
   <-->
   0
>>

interactive_rw flat_reduce_hyps_length_bind_cons {| reduce |} : <:xrewrite<
   hyps_length{mk_flat_vbind{| <J> >- mk_core{x :: l} |}}
   <-->
   hyps_length{mk_flat_vbind{| <J> >- mk_core{l} |}} +@ 1
>>

interactive_rw flat_reduce_hyps_length_bind_squashlist_cons {| reduce |} : <:xrewrite<
   hyps_length{mk_flat_vbind{| <J> >- mk_core{"squashlist"{| <K> >- x :: l |}} |}}
   <-->
   hyps_length{mk_flat_vbind{| <J> >- mk_core{"squashlist"{| <K> >- l |}} |}} +@ 1
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
