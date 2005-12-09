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
extends Meta_extensions_theory
extends Itt_pairwise
extends Itt_vec_bind
extends Itt_match
extends Itt_list3

doc docoff

open Basic_tactics
open Itt_struct
open Itt_squiggle

doc <:doc<
   The basic tool is a flattening operation, where given a list
   within a bind <:xterm< bind{x. [t_1; cdots; t_n]} >>, we produce
   a new flattened list <:xterm< [bind{x. t_1}; cdots; bind{x. t_n}] >>.

   This is the same trick from Itt_hoas_debruijn.  The reason
   why we repeat this process here is that we want to minimize
   well-formedness goals.  We would like the rewrites to work
   even if sequent is ill-formed.
>>
define unfold_hyps_length : hyps_length{'e} <--> <:xterm<
   (fix f e -> dest_bind{e; f bind_subst{e; "it"}; l. length{l}}) e
>>

define unfold_hyps_nth : hyps_nth{'e; 'i} <--> <:xterm<
   (fix f e -> dest_bind{e; mk_bind{x. f bind_subst{e; x}}; l. nth_elem{l; i}}) e
>>

define unfold_hyps_flatten : hyps_flatten{'e} <--> <:xterm<
   list_of_fun{k. hyps_nth{e; k}; hyps_length{e}}
>>

doc <:doc<
   The hypothesis list is constructed by sequent induction,
   flattening the list on each step.  This algorithm is quadratic,
   but since we only use it for computing representations, it
   doesn't matter.
>>
declare sequent [hypconslist] { Term : Term >- Term } : Term

prim_rw unfold_hypconslist : <:xrewrite<
   "hypconslist"{| <J> >- C |}
   <-->
   sequent_ind{u, v. u :: hyps_flatten{mk_bind{x. mk_core{happly{v; x}}}}; "TermSequent"{| <J> >- C |}}
>>

declare sequent [hyplist] { Term : Term >- Term } : Term

prim_rw unfold_hyplist : <:xrewrite<
   "hyplist"{| <J> >- C |}
   <-->
   "hypconslist"{| <J> >- [] |}
>>

doc <:doc<
   The bsequent is the sequent representation of a sequent triple.
>>
prim_rw unfold_bsequent : <:xrewrite<
   fsequent{arg}{| <J> >- C |}
   <-->
   (arg, "hyplist"{| <J> |}, "mk_vbind"{| <J> >- C |})
>>

(************************************************************************
 * Flattening properies.
 *)
doc docoff

let fold_hyps_length = makeFoldC << hyps_length{'e} >> unfold_hyps_length
let fold_hyps_nth = makeFoldC << hyps_nth{'e; 'i} >> unfold_hyps_nth
let fold_hyps_flatten = makeFoldC << hyps_flatten{'e} >> unfold_hyps_flatten
let fold_hypconslist = makeFoldC << hypconslist{| <J> >- 'C |} >> unfold_hypconslist
let fold_hyplist = makeFoldC << hyplist{| <J> |} >> unfold_hyplist

interactive_rw reduce_hyps_length_core {| reduce |} : <:xrewrite<
   hyps_length{mk_core{e}}
   <-->
   length{e}
>>

interactive_rw reduce_hyps_length_bind {| reduce |} : <:xrewrite<
   hyps_length{mk_bind{x. e[x]}}
   <-->
   hyps_length{e["it"]}
>>

interactive_rw reduce_hyps_nth_core {| reduce |} : <:xrewrite<
   hyps_nth{mk_core{e}; i}
   <-->
   nth_elem{e; i}
>>

interactive_rw reduce_hyps_nth_bind {| reduce |} : <:xrewrite<
   hyps_nth{mk_bind{x. e[x]}; i}
   <-->
   mk_bind{x. hyps_nth{e[x]; i}}
>>

interactive_rw reduce_hyps_flatten_core {| reduce |} : <:xrewrite<
   e IN "list" -->
   hyps_flatten{mk_core{e}}
   <-->
   e
>>

(************************************************************************
 * Basic hypconslist reductions.
 *)
interactive_rw reduce_hypconslist_concl {| reduce |} : <:xrewrite<
   "hypconslist"{| >- C |}
   <-->
   C
>>

interactive_rw reduce_hypconslist_left : <:xrewrite<
   "hypconslist"{| x: A; <J[x]> >- C[x] |}
   <-->
   A :: hyps_flatten{"mk_vbind"{| x : A >- mk_core{"hypconslist"{| <J[x]> >- C[x] |}} |}}
>>

interactive_rw reduce_hypconslist_right : <:xrewrite<
   "hypconslist"{| <J>; x: A >- C[x] |}
   <-->
   "hypconslist"{| <J> >- A :: hyps_flatten{"mk_vbind"{| x: A >- mk_core{C[x]} |}} |}
>>

interactive_rw reduce_hypconslist_shift {| reduce |} : <:xrewrite<
   "hypconslist"{| <J>; x: A >- "hypconslist"{| <K[x]> >- C[x] |} |}
   <-->
   "hypconslist"{| <J> >- "hypconslist"{| x: A; <K[x]> >- C[x] |} |}
>>

(************************************************************************
 * Well-formedness.
 *)
interactive hyps_length_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "list" -->
   <H> >- hyps_length{mk_core{e}} IN "nat"
>>

interactive hyps_flatten_is_list {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "list" -->
   <H> >- hyps_flatten{mk_core{e}} IN "list"
>>

interactive hypconslist_is_list {| intro [] |} : <:xrule<
   <H> >- "hypconslist"{| <J> >- [] |} IN "list"
>>

(************************************************************************
 * Hyps_length.
 *)
declare sequent [squashlist] { Term : Term >- Term } : Term

prim_rw unfold_squashlist : <:xrewrite<
   "squashlist"{| <J> >- C |}
   <-->
   sequent_ind{u, v. "it"::happly{v; "it"}; "TermSequent"{| <J> >- C |}}
>>

interactive_rw reduce_squashlist_concl {| reduce |} : <:xrewrite<
   "squashlist"{| >- C |}
   <-->
   C
>>

interactive_rw reduce_squashlist_left {| reduce |} : <:xrewrite<
   "squashlist"{| x: A; <J[x]> >- C[x] |}
   <-->
   "it" :: "squashlist"{| <J["it"]> >- C["it"] |}
>>

interactive_rw reduce_squashlist_right {| reduce |} : <:xrewrite<
   "squashlist"{| <J>; x: A >- C[x] |}
   <-->
   "squashlist"{| <J> >- "it"::C["it"] |}
>>

interactive_rw reduce_hyps_length_squashlist {| reduce |} : <:xrewrite<
   hyps_length{mk_core{"hypconslist"{| <J> >- [] |}}}
   <-->
   length{"squashlist"{| <J> >- [] |}}
>>

interactive_rw hoist_hyps_length 'i Perv!bind{x. 'S['x]} : <:xrewrite<
   i = hyps_length{"mk_vbind"{| <J> >- "hypconslist"{| <K> >- [] |} |}} in "nat" -->
   "mk_vbind"{| <J> >- S[hyps_length{"hypconslist"{| <K> >- [] |}}] |}
   <-->
   "mk_vbind"{| <J> >- S[i<||>] |}
>>

interactive_rw reduce_hyps_flatten_vec_nth_bind 'n : <:xrewrite<
   n IN "nat" -->
   i IN "nat" -->
   i < n -->
   "mk_vbind"{| <J> >- nth{hyps_flatten{mk_core{"hypconslist"{| <K> >- [] |}}}; i<||>} |}
   <-->
   "mk_vbind"{| <J> >- nth{"hypconslist"{| <K> >- [] |}; i} |}
>>

interactive_rw nth_inner {| reduce |} : <:xrewrite<
   nth{"hypconslist"{| <J> >- "hypconslist"{| x: A; <K[x]> >- [] |} |}; length{"hypconslist"{| <J> >- [] |}}}
   <-->
   "mk_vbind"{| <J> >- A |}
>>

(************************************************************************
 * Reductions to append.
 *)
interactive_rw nth_suffix_hypconslist : <:xrewrite<
   i = length{"hypconslist"{| <J> >- [] |}} in "nat" -->
   nth_suffix{"hypconslist"{| <J> >- C |}; i}
   <-->
   hyps_flatten{"mk_vbind"{| <J> >- C |}}
>>

interactive_rw nth_prefix_hypconslist_lemma : <:xrewrite<
   i = length{"hypconslist"{| <J> >- "vsubst_dummy"{| >- [] |} |}} in "nat" -->
   nth_prefix{"hypconslist"{| <J> >- "hypconslist"{| <K> >- [] |} |}; i}
   <-->
   nth_prefix{"hypconslist"{| <J> >- "hypconslist"{| >- [] |} |}; i}
>>

interactive_rw nth_prefix_hypconslist : <:xrewrite<
   i = length{"hypconslist"{| <J> >- [] |}} in "nat" -->
   nth_prefix{"hypconslist"{| <J> >- C |}; i}
   <-->
   "hypconslist"{| <J> >- [] |}
>>

interactive_rw hypconslist_nest_lemma {| reduce |} : <:xrewrite<
   "hypconslist"{| <J> >- C |}
   <-->
   append{"hypconslist"{| <J> >- [] |}; hyps_flatten{"mk_vbind"{| <J> >- C |}}}
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
