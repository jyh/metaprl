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

doc docoff

open Basic_tactics
open Itt_struct

declare Invalid_argument

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
   (fix f e -> dest_bind{e;
       mk_bind{x. f bind_subst{e; x}};
       l. list_ind{l; "Invalid_argument"; u, v, g. u}}) e
>>

define unfold_hyps_tl : hyps_tl{'e} <--> <:xterm<
   (fix f e -> dest_bind{e;
       mk_bind{x. f bind_subst{e; x}};
       l. list_ind{l; "Invalid_argument"; u, v, g. v}}) e
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
   hyps_hd{mk_core{e1 :: e2}}
   <-->
   e1
>>

interactive_rw reduce_hyps_hd_bind {| reduce |} : <:xrewrite<
   hyps_hd{mk_bind{x. e[x]}}
   <-->
   mk_bind{x. hyps_hd{e[x]}}
>>

interactive_rw reduce_hyps_tl_cons {| reduce |} : <:xrewrite<
   hyps_tl{mk_core{e1 :: e2}}
   <-->
   e2
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

(************************************************************************
 * Squiggle equality reasoning.
 *)
define unfold_Nil : Nil <--> <:xterm<
   Img{"unit"; x. []}
>>

define unfold_Cons : Cons <--> <:xterm<
   Img{"top" * "top"; x. let u, v = x in cons{u; v}}
>>

interactive nil_intro {| intro [] |} : <:xrule<
   <H> >- [] IN "Nil"
>>

interactive nil_elim {| elim [ThinOption thin] |} 'H : <:xrule<
   <H>; x: "Nil"; <J[ [] ]> >- C[ [] ] -->
   <H>; x: "Nil"; <J[x]> >- C[x]
>>

interactive cons_intro {| intro [] |} : <:xrule<
   <H> >- cons{e1; e2} IN "Cons"
>>

interactive cons_elim {| elim [] |} 'H : <:xrule<
   <H>; u: "top"; v: "top"; <J[cons{u; v}]> >- C[cons{u; v}] -->
   <H>; x: "Cons"; <J[x]> >- C[x]
>>

interactive cons_is_sqequal : <:xrule<
   "wf" : <H> >- e1 IN "Cons" -->
   "wf" : <H> >- e2 IN "Cons" -->
   <H> >- hd{e1} ~ hd{e2} -->
   <H> >- tl{e1} ~ tl{e2} -->
   <H> >- e1 ~ e2
>>

interactive_rw reduce_hyps_flatten_nil {| reduce |} : <:xrewrite<
   e["it"] IN "Nil" -->
   hyps_flatten{mk_bind{x. mk_core{e[x]}}}
   <-->
   []
>>

(************************************************************************
 * Vector lemmas.
 *)
declare sequent [vsubst_dummy] { Term : Term >- Term } : Term

prim_rw unfold_vsubst_dummy : <:xrewrite<
   "vsubst_dummy"{| <J> >- C |}
   <-->
   sequent_ind{u, v. happly{v; "it"}; "TermSequent"{| <J> >- C |}}
>>

interactive_rw reduce_vsubst_dummy_nil {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| >- C |}
   <-->
   C
>>

interactive_rw reduce_vsubst_dummy_left {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| x: A; <J[x]> >- C[x] |}
   <-->
   "vsubst_dummy"{| <J["it"]> >- C["it"] |}
>>

interactive_rw reduce_vsubst_dummy_right {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| <J>; x: A >- C[x] |}
   <-->
   "vsubst_dummy"{| <J> >- C["it"] |}
>>

interactive_rw reduce_vsubst_dummy_null : <:xrewrite<
   "vsubst_dummy"{| <J> >- e<||> |}
   <-->
   e
>>

interactive_rw reduce_vsubst_dummy_core {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| <J> >- mk_core{e} |}
   <-->
   mk_core{"vsubst_dummy"{| <J> >- e |}}
>>

interactive_rw reduce_vsubst_dummy_cons {| reduce |} : <:xrewrite<
   "vsubst_dummy"{| <J> >- e1 :: e2 |}
   <-->
   "vsubst_dummy"{| <J> >- e1 |} :: "vsubst_dummy"{| <J> >- e2 |}
>>

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
   "mk_vbind"{| <J> >- e2 |}
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
   "mk_vbind"{| <J> >- e1 |} :: hyps_flatten{"mk_vbind"{| <J> >- e2 |}}
>>

(************************************************************************
 * List reductions.
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

interactive_rw reduce_hypflatten_append0 : <:xrewrite<
   "hypconslist"{| >- hyps_flatten{"hypconslist"{| <J> >- C |}} |}
   <-->
   "hypconslist"{| >- append{"hypconslist"{| <J> >- [] |}; hyps_flatten{"mk_vbind"{| <J> >- C |}}} |}
>>

interactive_rw reduce_hypflatten_append1 : <:xrewrite<
   hyps_flatten{mk_bind{x. mk_core{append{"hypconslist"{| <J[x]> >- [] |}; e[x]}}}}
   <-->
   append{hyps_flatten{mk_bind{x. mk_core{"hypconslist"{| <J[x]> >- [] |}}}}; mk_bind{x. e[x]}}
>>

interactive_rw reduce_hypflatten_append {| reduce |} : <:xrewrite<
   hyps_flatten{mk_bind{x. mk_core{append{"hypconslist"{| <J[x]> >- [] |}; hyps_flatten{"mk_vbind"{| <J[x]> >- e[x] |}}}}}}
   <-->
   append{hyps_flatten{mk_bind{x. mk_core{"hypconslist"{| <J[x]> >- [] |}}}}; hyps_flatten{mk_bind{x. "mk_vbind"{| <J[x]> >- e[x] |}}}}
>>

interactive_rw hypconslist_nest_lemma {| reduce |} : <:xrewrite<
   "hypconslist"{| >- "hypconslist"{| <J> >- "hypconslist"{| <K> >- C |} |} |}
   <-->
   "hypconslist"{| >- append{"hypconslist"{| <J> >- [] |}; hyps_flatten{"mk_vbind"{| <J> >- mk_core{"hypconslist"{| <K> >- C |}} |}}} |}
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
