doc <:doc<
   Native sequent representation.  This representation of sequents
   is not a BTerm itself.  If you want to work in a theory where
   sequents are not part of your language, then you should probably
   use this representation, because it is easier to use.

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
extends Itt_hoas_vec_bind
extends Itt_hoas_sequent
extends Itt_match

doc docoff

open Basic_tactics

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
   (fix f e -> "decide"{e; _. f subst{e; "dummy_bterm"}; l. length{l}}) e
>>

define unfold_hyps_nth : hyps_nth{'e; 'i} <--> <:xterm<
   (fix f e -> "decide"{e; _. bind{x. f subst{e; x}}; l. nth{l; i}}) e
>>

define unfold_hyps_flatten : hyps_flatten{'e} <--> <:xterm<
   list_of_fun{i. hyps_nth{e; i}; hyps_length{e}}
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
   sequent_ind{u, v. u :: hyps_flatten{bind{x. inr{happly{v; x}}}}; "TermSequent"{| <J> >- C |}}
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
   bsequent{arg}{| <J> >- C |}
   <-->
   "sequent"{arg; "hyplist"{| <J> |}; "vbind"{| <J> >- C |}}
>>

doc <:doc<
   The hyps_ignore sequent is for discarding part of a term during induction.
>>
declare sequent [hyps_ignore] { Term : Term >- Term } : Term

prim_rw unfold_hyps_ignore : <:xrewrite<
   "hyps_ignore"{| <J> >- C |}
   <-->
   []
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

interactive_rw reduce_hyps_length_bind {| reduce |} : <:xrewrite<
   hyps_length{bind{x. e[x]}}
   <-->
   hyps_length{e["dummy_bterm"]}
>>

interactive_rw reduce_hyps_length_list {| reduce |} : <:xrewrite<
   hyps_length{inr{e}}
   <-->
   length{e}
>>

interactive_rw reduce_hyps_nth_list {| reduce |} : <:xrewrite<
   hyps_nth{inr{e}; i}
   <-->
   nth{e; i}
>>

interactive_rw reduce_hyps_nth_bind {| reduce |} : <:xrewrite<
   hyps_nth{bind{x. e[x]}; i}
   <-->
   bind{x. hyps_nth{e[x]; i}}
>>

interactive_rw reduce_hyps_nth_vec_bind {| reduce |} : <:xrewrite<
   hyps_nth{"vbind"{| <J> >- e |}; i}
   <-->
   "vbind"{| <J> >- hyps_nth{e; i} |}
>>

interactive_rw reduce_hyps_flatten_list {| reduce |} : <:xrewrite<
   e IN "list" -->
   hyps_flatten{inr{e}}
   <-->
   e
>>

(************************************************************************
 * Vector hyps_length.
 *)
declare sequent [vsubst_dummy] { Term : Term >- Term } : Term

prim_rw unfold_vsubst_dummy : <:xrewrite<
   "vsubst_dummy"{| <J> >- C |}
   <-->
   sequent_ind{u, v. happly{v; "dummy_bterm"}; "TermSequent"{| <J> >- C |}}
>>

interactive_rw reduce_vsubst_dummy_nil {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| >- C |}
   <-->
   C
>>

interactive_rw reduce_vsubst_dummy_left {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| x: A; <J[x]> >- C[x] |}
   <-->
   "vsubst_dummy"{| <J["dummy_bterm"]> >- C["dummy_bterm"] |}
>>

interactive_rw reduce_vsubst_dummy_right {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| <J>; x: A >- C[x] |}
   <-->
   "vsubst_dummy"{| <J> >- C["dummy_bterm"] |}
>>

interactive_rw reduce_subst_dummy_null : <:xrewrite<
   "vsubst_dummy"{| <J> >- e<||> |}
   <-->
   e
>>

interactive_rw reduce_subst_dummy_inr {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| <J> >- inr{e} |}
   <-->
   inr{"vsubst_dummy"{| <J> >- e |}}
>>

interactive_rw reduce_subst_dummy_cons {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| <J> >- e1 :: e2 |}
   <-->
   "vsubst_dummy"{| <J> >- e1 |} :: "vsubst_dummy"{| <J> >- e2 |}
>>

interactive_rw hyps_length_shift {| reduce |} : <:xrewrite<
   hyps_length{"vbind"{| <J> >- e |}}
   <-->
   hyps_length{"vsubst_dummy"{| <J> >- e |}}
>>

interactive_rw hyps_length_vec_nil {| reduce |} : <:xrewrite<
   hyps_length{"vbind"{| <J> >- inr{[]} |}}
   <-->
   0
>>

interactive_rw hyps_length_vec_cons {| reduce |} : <:xrewrite<
   hyps_length{"vbind"{| <J> >- inr{e1 :: e2} |}}
   <-->
   hyps_length{"vbind"{| <J> >- inr{e2} |}} +@ 1
>>

(************************************************************************
 * Vector hyps_flatten.
 *)
interactive_rw hyps_flatten_nil {| reduce |} : <:xrewrite<
   hyps_flatten{"vbind"{| <J> >- inr{[]} |}}
   <-->
   []
>>

interactive_rw hyps_flatten_cons {| reduce |} : <:xrewrite<
   hyps_flatten{"vbind"{| <J> >- inr{e1 :: e2} |}}
   <-->
   "vbind"{| <J> >- e1 |} :: hyps_flatten{"vbind"{| <J> >- inr{e2} |}}
>>

(************************************************************************
 * Hyplist properties.
 *)
interactive_rw reduce_hypconslist_concl {| reduce |} : <:xrewrite<
   "hypconslist"{| >- C |}
   <-->
   C
>>

interactive_rw reduce_hypconslist_shift : <:xrewrite<
   "hypconslist"{| <J>; x: A >- "hypconslist"{| <K[x]> >- C[x] |} |}
   <-->
   "hypconslist"{| <J> >- "hypconslist"{| x: A; <K[x]> >- C[x] |} |}
>>

interactive_rw reduce_hypconslist_split 'J : <:xrewrite<
   "hypconslist"{| <J>; <K> >- C |}
   <-->
   "hypconslist"{| <J> >- "hypconslist"{| <K> >- C |} |}
>>

(************************************************
 * Split the nested lists into appends.
 *)
interactive_rw reduce_hypconslist_shift_append_lemma : <:xrewrite<
   hyps_flatten{"vbind"{| >- inr{"hypconslist"{| <J>; x: A >- [] |}} |}}
   <-->
   hyps_flatten{"vbind"{| >- inr{append{"hypconslist"{| <J> >- [] |}; hyps_flatten{"vbind"{| <J> >- inr{[A]} |}}}} |}}
>>

interactive_rw reduce_hypconslist_append : <:xrewrite<
   "hypconslist"{| <J> >- "hypconslist"{| <K> >- [] |} |}
   <-->
   append{"hypconslist"{| <J> >- "hyps_ignore"{| <K> >- [] |} |}; hyps_flatten{"vbind"{| <J> >- "hypconslist"{| <K> >- [] |} |}}}
>>

interactive_rw reduce_hyplist_right {| reduce |} : <:xrewrite<
   "hyplist"{| <J>; A |}
   <-->
   append{"hyplist"{| <J> |}; ["vbind"{| <J> >- A |}]}
>>

interactive_rw reduce_hyplist_length : <:xrewrite<
   "hyplist"{| <J> |} IN CVar{0} -->
   length{"hyplist"{| <J> |}}
   <-->
   bdepth{"vbind"{| <J> >- "dummy_bterm" |}}
>>

(************************************************************************
 * Well-formedness.
 *)
declare sequent [sequent_wf] { Term : Term >- Term } : Term

prim_rw unfold_sequent_wf : <:xrewrite<
   "sequent_wf"{| <J> >- C |}
   <-->
   "hyplist"{| <J> |} IN CVar{0} && "vbind"{| <J> >- C |} IN BTerm{bdepth{"vbind"{| <J> >- "dummy_bterm" |}}}
>>

(************************************************************************
 * The wf theorem.
 *)
interactive bsequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- arg IN BTerm{0} -->
   "wf" : <H> >- "sequent_wf"{| <J> >- C |} -->
   <H> >- bsequent{arg}{| <J> >- C |} IN "Sequent"
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
