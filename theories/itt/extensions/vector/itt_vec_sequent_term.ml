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
define unfold_hyps_are_nil : hyps_are_nil{'e} <--> <:xterm<
   (fix f e ->
       dest_bind{e;
          f bind_subst{e; "it"};
          l. list_ind{l; btrue; u, v, g. bfalse}}) e
>>

define unfold_hyps_hd : hyps_hd{'e} <--> <:xterm<
   (fix f e -> dest_bind{e; mk_bind{x. f bind_subst{e; x}}; l. hd{l}}) e
>>

define unfold_hyps_tl : hyps_tl{'e} <--> <:xterm<
   (fix f e -> dest_bind{e; mk_bind{x. f bind_subst{e; x}}; l. mk_core{tl{l}}}) e
>>

define unfold_hyps_flatten : hyps_flatten{'e} <--> <:xterm<
   (fix f e ->
      if hyps_are_nil{e} then
         []
      else
         hyps_hd{e} :: f hyps_tl{e}) e
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

let fold_hyps_are_nil = makeFoldC << hyps_are_nil{'e} >> unfold_hyps_are_nil
let fold_hyps_hd = makeFoldC << hyps_hd{'e} >> unfold_hyps_hd
let fold_hyps_tl = makeFoldC << hyps_tl{'e} >> unfold_hyps_tl
let fold_hyps_flatten = makeFoldC << hyps_flatten{'e} >> unfold_hyps_flatten
let fold_hypconslist = makeFoldC << hypconslist{| <J> >- 'C |} >> unfold_hypconslist
let fold_hyplist = makeFoldC << hyplist{| <J> |} >> unfold_hyplist

interactive_rw reduce_hyps_are_nil_nil {| reduce |} : <:xrewrite<
   hyps_are_nil{mk_core{[]}}
   <-->
   btrue
>>

interactive_rw reduce_hyps_are_nil_cons {| reduce |} : <:xrewrite<
   hyps_are_nil{mk_core{e1 :: e2}}
   <-->
   bfalse
>>

interactive_rw reduce_hyps_are_nil_bind {| reduce |} : <:xrewrite<
   hyps_are_nil{mk_bind{x. e[x]}}
   <-->
   hyps_are_nil{e["it"]}
>>

interactive_rw reduce_hyps_hd_cons {| reduce |} : <:xrewrite<
   hyps_hd{mk_core{e}}
   <-->
   hd{e}
>>

interactive_rw reduce_hyps_hd_bind {| reduce |} : <:xrewrite<
   hyps_hd{mk_bind{x. e[x]}}
   <-->
   mk_bind{x. hyps_hd{e[x]}}
>>

interactive_rw reduce_hyps_tl_cons {| reduce |} : <:xrewrite<
   hyps_tl{mk_core{e}}
   <-->
   mk_core{tl{e}}
>>

interactive_rw reduce_hyps_tl_bind {| reduce |} : <:xrewrite<
   hyps_tl{mk_bind{x. e[x]}}
   <-->
   mk_bind{x. hyps_tl{e[x]}}
>>

interactive_rw reduce_hyps_flatten : <:xrewrite<
   hyps_flatten{e}
   <-->
   if hyps_are_nil{e} then
      []
   else
      hyps_hd{e} :: hyps_flatten{hyps_tl{e}}
>>

interactive_rw reduce_hyps_flatten_nil {| reduce |} : <:xrewrite<
   hyps_flatten{mk_core{[]}}
   <-->
   []
>>

interactive_rw reduce_hyps_flatten_cons {| reduce |} : <:xrewrite<
   hyps_flatten{mk_core{e1 :: e2}}
   <-->
   e1 :: hyps_flatten{mk_core{e2}}
>>

(************************************************************************
 * Vector lemmas.
 *)

(*
 * hyps_are_nil reductions.
 *)
interactive_rw reduce_hyps_are_nil_vec_nil {| reduce |} : <:xrewrite<
   hyps_are_nil{"mk_vbind"{| <J> >- mk_core{[]} |}}
   <-->
   "btrue"
>>

interactive_rw reduce_hyps_are_nil_vec_cons {| reduce |} : <:xrewrite<
   hyps_are_nil{"mk_vbind"{| <J> >- mk_core{e1 :: e2} |}}
   <-->
   "bfalse"
>>

(*
 * Hyps projection reductions.
 *)
interactive_rw reduce_hyps_hd_vec {| reduce |} : <:xrewrite<
   hyps_hd{"mk_vbind"{| <J> >- mk_core{e1 :: e2} |}}
   <-->
   "mk_vbind"{| <J> >- e1 |}
>>

interactive_rw reduce_hyps_tl_vec {| reduce |} : <:xrewrite<
   hyps_tl{"mk_vbind"{| <J> >- mk_core{e1 :: e2} |}}
   <-->
   "mk_vbind"{| <J> >- mk_core{e2} |}
>>

(*
 * Hyps_flatten reductions.
 *)
interactive_rw reduce_hyps_flatten_vec_nil {| reduce |} : <:xrewrite<
   hyps_flatten{"mk_vbind"{| <J> >- mk_core{[]} |}}
   <-->
   []
>>

interactive_rw reduce_hyps_flatten_vec_cons {| reduce |} : <:xrewrite<
   hyps_flatten{"mk_vbind"{| <J> >- mk_core{e1 :: e2} |}}
   <-->
   "mk_vbind"{| <J> >- e1 |} :: hyps_flatten{"mk_vbind"{| <J> >- mk_core{e2} |}}
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
 * Sloppy list reductions.
 *)
interactive hyps_flatten_cons {| intro [] |} : <:xrule<
   "wf" : <H> >- e["it"] IN "Cons" -->
   <H> >- hyps_flatten{mk_bind{x. mk_core{e[x]}}} IN "Cons"
>>

interactive hyps_flatten_cons_depth {| intro [] |} : <:xrule<
   "wf" : <H> >- n IN "nat" -->
   "wf" : <H> >- e["it"] IN Cons{n} -->
   <H> >- hyps_flatten{mk_bind{x. mk_core{e[x]}}} IN Cons{n}
>>

interactive hyps_flatten_list {| intro [] |} : <:xrule<
   "wf" : <H> >- e["it"] IN "list" -->
   <H> >- hyps_flatten{mk_bind{x. mk_core{e[x]}}} IN "list"
>>

interactive_rw reduce_hyps_flatten_length_bind {| reduce |} : <:xrewrite<
   e["it"] IN "list" -->
   length{hyps_flatten{mk_bind{x. mk_core{e[x]}}}}
   <-->
   length{hyps_flatten{mk_core{e["it"]}}}
>>

interactive_rw reduce_hyps_flatten_length_list {| reduce |} : <:xrewrite<
   e IN "list" -->
   length{hyps_flatten{mk_core{e}}}
   <-->
   length{e}
>>

interactive_rw reduce_hyps_flatten_nth_bind 'n : <:xrewrite<
   n IN "nat" -->
   i IN "nat" -->
   i < n -->
   e["it"] IN Cons{n} -->
   nth_elem{hyps_flatten{mk_bind{x. mk_core{e[x]}}}; i}
   <-->
   mk_bind{x. nth_elem{e[x]; i}}
>>

interactive_rw reduce_hyps_flatten_bind_nth 'n : <:xrewrite<
   n IN "nat" -->
   i IN "nat" -->
   i < n -->
   e["it"] IN Cons{n} -->
   mk_bind{x. nth_elem{hyps_flatten{mk_core{e[x]}}; i}}
   <-->
   mk_bind{x. nth_elem{e[x]; i}}
>>

interactive_rw reduce_hyps_flatten_nth_vec_bind 'n : <:xrewrite<
   n IN "nat" -->
   i IN "nat" -->
   i < n -->
   "vsubst_dummy"{| <J> >- e |} IN Cons{n} -->
   nth_elem{hyps_flatten{"mk_vbind"{| <J> >- mk_core{e} |}}; i}
   <-->
   "mk_vbind"{| <J> >- nth_elem{e; i} |}
>>

interactive_rw reduce_hyps_flatten_vec_nth_bind 'n : <:xrewrite<
   n IN "nat" -->
   i IN "nat" -->
   i < n -->
   "vsubst_dummy"{| <J> >- e["it"] |} IN Cons{n} -->
   "mk_vbind"{| <J> >- nth_elem{hyps_flatten{mk_bind{x. mk_core{e[x]}}}; i<||>} |}
   <-->
   "mk_vbind"{| <J> >- mk_bind{x. nth_elem{e[x]; i}} |}
>>

(************************************************************************
 * Reductions to append.
 *)
interactive hypconslist_is_list {| intro [] |} : <:xrule<
   <H> >- "hypconslist"{| <J> >- [] |} IN "list"
>>

interactive hypconslist_is_cons {| intro [] |} : <:xrule<
   <H> >- "hypconslist"{| <J> >- C |} IN Cons{length{"hypconslist"{| <J> >- [] |}}}
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
