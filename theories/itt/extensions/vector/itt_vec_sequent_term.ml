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
extends Itt_vec_dform
extends Itt_pairwise
extends Itt_vec_bind
extends Itt_match
extends Itt_list3
extends Itt_list_sloppy

doc docoff

open Lm_printf
open Basic_tactics
open Simple_print
open Itt_struct
open Itt_squiggle
open Itt_vec_bind
open Itt_logic
open Itt_equal

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
   (fix f e -> dest_bind{e; mk_bind{x. f bind_subst{e; x}}; l. nth{l; i}}) e
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
   sequent_ind{u, v. mk_core{u} :: hyps_flatten{mk_bind{x. mk_core{happly{v; x}}}}; "TermSequent"{| <J> >- C |}}
>>

declare sequent [hyplist] { Term : Term >- Term } : Term

prim_rw unfold_hyplist : <:xrewrite<
   "hyplist"{| <J> >- C |}
   <-->
   "hypconslist"{| <J> >- [] |}
>>

doc <:doc<
   The @tt[fsequent] is the sequent representation of a sequent triple.
>>
prim_rw unfold_fsequent : <:xrewrite<
   fsequent{arg}{| <J> >- C |}
   <-->
   (arg, "hyplist"{| <J> |}, "mk_vbind"{| <J> >- mk_core{C} |})
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
   nth{e; i}
>>

interactive_rw reduce_hyps_nth_bind {| reduce |} : <:xrewrite<
   hyps_nth{mk_bind{x. e[x]}; i}
   <-->
   mk_bind{x. hyps_nth{e[x]; i}}
>>

interactive_rw reduce_hyps_flatten_core {| reduce |} : <:xrewrite<
   e in list -->
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
   mk_core{A} :: hyps_flatten{"mk_vbind"{| x : A >- mk_core{"hypconslist"{| <J[x]> >- C[x] |}} |}}
>>

interactive_rw reduce_hypconslist_right : <:xrewrite<
   "hypconslist"{| <J>; x: A >- C[x] |}
   <-->
   "hypconslist"{| <J> >- mk_core{A} :: hyps_flatten{"mk_vbind"{| x: A >- mk_core{C[x]} |}} |}
>>

interactive_rw reduce_hypconslist_shift {| reduce |} : <:xrewrite<
   "hypconslist"{| <J>; x: A >- "hypconslist"{| <K[x]> >- C[x] |} |}
   <-->
   "hypconslist"{| <J> >- "hypconslist"{| x: A; <K[x]> >- C[x] |} |}
>>

interactive_rw reduce_hypconslist_merge : <:xrewrite<
   "hypconslist"{| <J> >- "hypconslist"{| <K> >- [] |} |}
   <-->
   "hypconslist"{| <J>; <K> >- [] |}
>>

(************************************************************************
 * Hyps length.
 *)
doc <:doc<
   The following section defines the internal rewrites on @tt[hyps_length].

   The key to getting rewriting to work in general is to lift the destructor
   @tt[hyps_length] out of the scope of binders, allowing a case analysis
   to be performed.

   Consider the following term.
   << mk_vbind{| <J> >- hyps_length{mk_core{hypconslist{| <K> >- nil |}}} |} >>
   Even though the @tt[hyps_length] is in the scope of the binders
   @code{<J>}, and the values @code{<K>} depend on @code{<J>}, the
   length does not depend on the values of the individual terms in @code{<K>}.
   On the surface, it seems like it should be easy to rewrite within the
   scope of the binders.

   However, rewriting in the scope of a binder is hard in general.
   Any kind of destructor that has a side condition will fail.  For example,
   the induction combinator for natural numbers has a side-condition that
   requires that its argument be a natural number.  With some work, the
   side-condition can be hoisted, but the many occurrences of such
   arguments are painful.

   As a workaround, we introduce the << squashlist{| <J> >- 'l |} >> term,
   which reduces to an << it >> list (a << list{unit} >>), squashing
   the hypothesis values.  We also establish the equivalence
   << hyps_length{mk_core{hypconslist{| <J> >- nil |}}} ~ length{squashlist{| <J> >- nil |}} >>
   as an unconditional rewrite.  Once converted to a @tt[squashlist], the
   dependencies can be broken, and the length term can be hoisted out of the scope
   of the binders.

   Literally, the use of @tt[squashlist] doesn't break any dependencies
   immediately.  However, by ``shaking'' it back and forth (using induction),
   we can show that in any particular case the dependencies do not matter.
>>
declare sequent [squashlist] { Term : Term >- Term } : Term

prim_rw unfold_squashlist : <:xrewrite<
   "squashlist"{| <J> >- C |}
   <-->
   sequent_ind{u, v. "it"::happly{v; "it"}; "TermSequent"{| <J> >- C |}}
>>

doc docoff

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

interactive squashlist_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l IN "list" -->
   <H> >- "squashlist"{| <J> >- l<|H|> |} IN "list"
>>

interactive squashlist_length_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l IN "list" -->
   <H> >- length{"squashlist"{| <J> >- l<|H|> |}} IN "nat"
>>

(************************************************************************
 * Well-formedness.
 *)
interactive hyps_length_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "list" -->
   <H> >- hyps_length{mk_core{e}} IN "nat"
>>

interactive hyps_length_wf2 {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "list" -->
   <H> >- hyps_length{"mk_vbind"{| <J> >- mk_core{e<|H|>} |}} IN "nat"
>>

interactive hyps_flatten_is_list {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "list" -->
   <H> >- hyps_flatten{mk_core{e}} IN "list"
>>

interactive hypconslist_is_list {| intro [] |} : <:xrule<
   <H> >- "hypconslist"{| <J> >- [] |} IN "list"
>>

interactive hypconslist_is_list2 {| intro [] |} : <:xrule<
   "wf" : <H> >- l IN "list" -->
   <H> >- "hypconslist"{| <J> >- l<|H|> |} IN "list"
>>

interactive hypconslist_is_list3 {| intro [] |} : <:xrewrite<
   <H> >- "hypconslist"{| <J> >- "hypconslist"{| <K> >- [] |} |} IN "list"
>>

interactive hyps_length_bind_hypconslist_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l IN "list" -->
   <H> >- hyps_length{"mk_vbind"{| <J> >- mk_core{"hypconslist"{| <K> >- l<|H|> |}} |}} IN "nat"
>>

interactive hyps_length_bind_squashlist_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l IN "list" -->
   <H> >- hyps_length{"mk_vbind"{| <J> >- mk_core{"squashlist"{| <K> >- l<|H|> |}} |}} IN "nat"
>>

interactive hyps_flatten_bind_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l IN "list" -->
   <H> >- hyps_flatten{"mk_vbind"{| <J> >- mk_core{"hypconslist"{| <K> >- l<||> |}} |}} IN "list"
>>

(************************************************
 * Hyps length reductions.
 *)
interactive_rw reduce_hyps_length_squashlist : <:xrewrite<
   hyps_length{mk_core{"hypconslist"{| <J> >- [] |}}}
   <-->
   length{"squashlist"{| <J> >- [] |}}
>>

interactive_rw reduce_hyps_length_squashlist_list {| reduce |} : <:xrewrite<
   l IN "list" -->
   hyps_length{mk_core{"hypconslist"{| <J> >- l<||> |}}}
   <-->
   length{"squashlist"{| <J> >- l |}}
>>

interactive_rw reduce_hyps_length_bind_squashlist {| reduce |} : <:xrewrite<
   l IN "list" -->
   hyps_length{"mk_vbind"{| <J> >- mk_core{"hypconslist"{| <K> >- l<||> |}} |}}
   <-->
   hyps_length{"mk_vbind"{| <J> >- mk_core{"squashlist"{| <K> >- l |}} |}}
>>

(************************************************
 * Length reductions.
 *)
interactive_rw reduce_length_hypconslist {| reduce |} : <:xrewrite<
   l IN "list" -->
   length{"hypconslist"{| <J> >- l<||> |}}
   <-->
   length{"squashlist"{| <J> >- l |}}
>>

interactive_rw reduce_hyps_length_right {| reduce |} : <:xrewrite<
   l IN "list" -->
   length{"hypconslist"{| <J>; x: A >- l<||> |}}
   <-->
   length{"hypconslist"{| <J> >- l |}} +@ 1
>>

interactive hypconslist_length_lt {| intro [] |} : <:xrewrite<
   <H> >- length{"hypconslist"{| <J> >- [] |}} <= length{"hypconslist"{| <J> >- "hypconslist"{| <K> >- [] |} |}}
>>

interactive_rw reduce_hyps_flatten_length {| reduce |} : <:xrewrite<
   l IN "list" -->
   length{hyps_flatten{"mk_vbind"{| <J> >- mk_core{"hypconslist"{| <K> >- l<||> |}} |}}}
   <-->
   hyps_length{"mk_vbind"{| <J> >- mk_core{"hypconslist"{| <K> >- l |}} |}}
>>

(************************************************
 * Now the hoisting lemmas for occurrences
 * of << hyps_length{'e} >>.
 *)
interactive_rw hyps_length_null : <:xrewrite<
   hyps_length{"mk_vbind"{| <J> >- mk_core{l<||>} |}}
   <-->
   length{l}
>>

interactive_rw hyps_length_bind_int 'i : <:xrewrite<
   i = hyps_length{"mk_vbind"{| <J> >- mk_core{"hypconslist"{| <K> >- [] |}} |}} in "nat" -->
   "mk_vbind"{| <J> >- hyps_length{mk_core{"hypconslist"{| <K> >- [] |}}} |}
   <-->
   "mk_vbind"{| <J> >- i<||> |}
>>

interactive_rw hoist_hyps_length 'i Perv!bind{x. 'S['x]} : <:xrewrite<
   i = hyps_length{"mk_vbind"{| <J> >- mk_core{"hypconslist"{| <K> >- [] |}} |}} in "nat" -->
   "mk_vbind"{| <J> >- S[hyps_length{mk_core{"hypconslist"{| <K> >- [] |}}}] |}
   <-->
   "mk_vbind"{| <J> >- S[i<||>] |}
>>

interactive_rw hyps_length_bind_int_vec 'i : <:xrewrite<
   i = hyps_length{"mk_vbind"{| <J>; <K> >- mk_core{"squashlist"{| <L> >- [] |}} |}} in "nat" -->
   "mk_vbind"{| <J> >- hyps_length{"mk_vbind"{| <K> >- mk_core{"squashlist"{| <L> >- [] |}} |}} |}
   <-->
   "mk_vbind"{| <J> >- i<||> |}
>>

interactive_rw hoist_hyps_length_vec 'i Perv!bind{x. 'S['x]} : <:xrewrite<
   i = hyps_length{"mk_vbind"{| <J>; <K> >- mk_core{"squashlist"{| <L> >- [] |}} |}} in "nat" -->
   "mk_vbind"{| <J> >- S[hyps_length{"mk_vbind"{| <K> >- mk_core{"squashlist"{| <L> >- [] |}} |}}] |}
   <-->
   "mk_vbind"{| <J> >- S[i<||>] |}
>>

interactive_rw reduce_hyps_nth_vec_bind {| reduce |} : <:xrewrite<
   "mk_vbind"{| <J> >- hyps_nth{"mk_vbind"{| <K> >- mk_core{"hypconslist"{| <L> >- [] |}} |}; i<||>} |}
   <-->
   "mk_vbind"{| <J>; <K> >- nth{"hypconslist"{| <L> >- [] |}; i} |}
>>

interactive_rw reduce_hyps_nth_vec_bind_tail {| reduce |} : <:xrewrite<
   hyps_nth{"mk_vbind"{| <K> >- mk_core{"hypconslist"{| <L> >- [] |}} |}; i<||>}
   <-->
   "mk_vbind"{| <K> >- nth{"hypconslist"{| <L> >- [] |}; i} |}
>>

interactive_rw reduce_hyps_length_bind_right {| reduce |} : <:xrewrite<
   hyps_length{"mk_vbind"{| <J>; x: A >- mk_core{"squashlist"{| <K[x]> >- [] |}} |}}
   <-->
   hyps_length{"mk_vbind"{| <J> >- mk_core{"squashlist"{| <K["it"]> >- [] |}} |}}
>>

interactive_rw reduce_hyps_length_bind_nil {| reduce |} : <:xrewrite<
   hyps_length{"mk_vbind"{| <J> >- mk_core{[]} |}}
   <-->
   0
>>

interactive_rw reduce_hyps_length_bind_cons {| reduce |} : <:xrewrite<
   hyps_length{"mk_vbind"{| <J> >- mk_core{x :: l} |}}
   <-->
   hyps_length{"mk_vbind"{| <J> >- mk_core{l} |}} +@ 1
>>

interactive_rw reduce_hyps_length_bind_squashlist_cons {| reduce |} : <:xrewrite<
   hyps_length{"mk_vbind"{| <J> >- mk_core{"squashlist"{| <K> >- x :: l |}} |}}
   <-->
   hyps_length{"mk_vbind"{| <J> >- mk_core{"squashlist"{| <K> >- l |}} |}} +@ 1
>>

(************************************************
 * hyps_flatten reductions.
 *)
interactive_rw reduce_nth_of_list_of_fun {| reduce |} : <:xrewrite<
   n IN "nat" -->
   j IN "nat" -->
   j < n -->
   nth{list_of_fun{i. f[i]; n}; j}
   <-->
   f[j]
>>

interactive_rw reduce_hyps_nth_flatten_bind {| reduce |} : <:xrewrite<
   i IN "nat" -->
   i < hyps_length{"mk_vbind"{| <J>; <K> >- mk_core{"hypconslist"{| <L> >- [] |}} |}} -->
   "mk_vbind"{| <J> >- hyps_nth{mk_core{hyps_flatten{"mk_vbind"{| <K> >- mk_core{"hypconslist"{| <L> >- [] |}} |}}}; i<||>} |}
   <-->
   "mk_vbind"{| <J>; <K> >- nth{"hypconslist"{| <L> >- [] |}; i} |}
>>

interactive_rw reduce_hyps_nth_flatten_bind_normalized {| reduce |} : <:xrewrite<
   i IN "nat" -->
   i < hyps_length{"mk_vbind"{| <J>; <K> >- mk_core{"hypconslist"{| <L> >- [] |}} |}} -->
   "mk_vbind"{| <J> >- nth{hyps_flatten{"mk_vbind"{| <K> >- mk_core{"hypconslist"{| <L> >- [] |}} |}}; i<||>} |}
   <-->
   "mk_vbind"{| <J>; <K> >- nth{"hypconslist"{| <L> >- [] |}; i} |}
>>

interactive_rw reduce_hyps_flatten_bind_cons {| reduce |} : <:xrewrite<
   hyps_flatten{"mk_vbind"{| <J> >- mk_core{"hypconslist"{| x: A; <K[x]> >- [] |}} |}}
   <-->
   "mk_vbind"{| <J> >- mk_core{A} |} :: hyps_flatten{"mk_vbind"{| <J>; x: A >- mk_core{"hypconslist"{| <K[x]> >- [] |}} |}}
>>

interactive_rw reduce_hyps_flatten_bind_nil1 {| reduce |} : <:xrewrite<
   hyps_flatten{"mk_vbind"{| <J> >- mk_core{hypconslist{| >- [] |}} |}}
   <-->
   []
>>

interactive_rw reduce_hyps_flatten_bind_nil2 {| reduce |} : <:xrewrite<
   hyps_flatten{"mk_vbind"{| <J> >- mk_core{[]} |}}
   <-->
   []
>>

(************************************************************************
 * Reductions to append.
 *)
interactive_rw nth_suffix_hypconslist {| reduce |} : <:xrewrite<
   i = length{"hypconslist"{| <J> >- [] |}} in "nat" -->
   nth_suffix{"hypconslist"{| <J> >- "hypconslist"{| <K> >- [] |} |}; i}
   <-->
   hyps_flatten{"mk_vbind"{| <J> >- mk_core{"hypconslist"{| <K> >- [] |}} |}}
>>

interactive_rw nth_prefix_hypconslist {| reduce |} : <:xrewrite<
   i = length{"hypconslist"{| <J> >- [] |}} in "nat" -->
   nth_prefix{"hypconslist"{| <J> >- "hypconslist"{| <K> >- [] |} |}; i}
   <-->
   "hypconslist"{| <J> >- [] |}
>>

interactive_rw hypconslist_nest_lemma {| reduce |} : <:xrewrite<
   "hypconslist"{| <J> >- "hypconslist"{| <K> >- [] |} |}
   <-->
   append{"hypconslist"{| <J> >- [] |}; hyps_flatten{"mk_vbind"{| <J> >- mk_core{"hypconslist"{| <K> >- [] |}} |}}}
>>

interactive_rw hypconslist_nest 'J : <:xrewrite<
   "hypconslist"{| <J>; <K> >- [] |}
   <-->
   append{"hypconslist"{| <J> >- [] |}; hyps_flatten{"mk_vbind"{| <J> >- mk_core{"hypconslist"{| <K> >- [] |}} |}}}
>>

interactive_rw hyplist_nest 'J : <:xrewrite<
   "hyplist"{| <J>; <K> |}
   <-->
   append{"hyplist"{| <J> |}; hyps_flatten{"mk_vbind"{| <J> >- mk_core{"hyplist"{| <K> |}} |}}}
>>

interactive_rw reduce_hyplist_nil {| reduce |} : <:xrewrite<
   "hyplist"{||}
   <-->
   []
>>

interactive_rw reduce_hyplist_left : <:xrewrite<
   "hyplist"{| x: A; <J[x]> |}
   <-->
   mk_core{A} :: hyps_flatten{mk_bind{x. mk_core{"hyplist"{| <J[x]> |}}}}
>>

(************************************************************************
 * hyplist rewrites and well-formedness.
 *)
interactive hyplist_wf {| intro [] |} : <:xrule<
   <H> >- "hyplist"{| <J> |} IN "list"
>>

interactive hyplist_flatten_wf {| intro [] |} : <:xrule<
   <H> >- hyps_flatten{"mk_vbind"{| <J> >- mk_core{"hyplist"{| <K> |}} |}} IN "list"
>>

interactive_rw reduce_hyplist_single {| reduce |} : <:xrule<
   "hyplist"{| x: A |}
   <-->
   [mk_core{A}]
>>

interactive_rw reduce_hyplist_flatten_single {| reduce |} : <:xrule<
   hyps_flatten{"mk_vbind"{| <J> >- mk_core{"hyplist"{| x: A |}} |}}
   <-->
   ["mk_vbind"{| <J> >- mk_core{A} |}]
>>

(************************************************************************
 * Tactics.
 *)
let hyps_length_term = << hyps_length{'e} >>
let hyps_length_opname = opname_of_term hyps_length_term
let is_hyps_length_term = is_dep0_term hyps_length_opname
let dest_hyps_length_term = dest_dep0_term hyps_length_opname
let mk_hyps_length_term = mk_dep0_term hyps_length_opname

let hyplist_arg_term = << hyplist >>
let hyplist_arg_opname = opname_of_term hyplist_arg_term
let is_hyplist_arg_term = is_no_subterms_term hyplist_arg_opname
let is_hyplist_term t =
   is_sequent_term t && is_hyplist_arg_term (TermMan.args t)

let dest_hyplist_term t =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in
      if is_hyplist_arg_term arg then
         hyps
      else
         raise (RefineError ("dest_hyp_context_term", StringTermError ("not a hyplist term", t)))

let t_nat = << nat >>

let var_i = Lm_symbol.add "i"

let hoist_hyps_length_tac p =
   let t = concl p in
   let info = all_vars_info SymbolTable.empty t in
   let fv = SymbolTable.fold (fun fv v _ -> SymbolSet.add fv v) SymbolSet.empty info in
   let v_i = maybe_new_var_set var_i fv in
   let t_i = mk_var_term v_i in

   (*
    * Find a term mk_vbind{| <J> >- S[hyps_length{e}] |} at address "addr"
    * and return a 4-tuple:
    *
    *    addr, <J>, bind{x. S[x]}, hyps_length{e}
    *)
   let rec search addrs =
      match addrs with
         addr1 :: addrs ->
            let t_vbind = term_subterm t addr1 in
            let { sequent_hyps = hyps;
                  sequent_concl = c
                } = explode_sequent t_vbind
            in
               (match find_subterm c (fun t _ -> is_hyps_length_term t) with
                   addr2 :: _ ->
                      let t_length = term_subterm c addr2 in
                      let t_var = replace_subterm c addr2 (mk_var_term v_i) in
                      let t_bind = mk_bind1_term v_i t_var in
                      let addr1 = dest_address addr1 in
                         addr1, hyps, t_bind, t_length
                 | [] ->
                      search addrs)
       | [] ->
            raise (RefineError ("hoist_hyps_length_conv", StringError "no hyps_length subterm"))
   in
   let addrs = find_subterm t (fun t _ -> is_mk_vbind_term t) in
   let addr, hyps, t_bind, t_length = search addrs in

   (*
    * Build the term hyps_length{mk_vbind{| <J> >- e |}}
    *)
   let e = dest_hyps_length_term t_length in
   let t_length, conv =
      if is_mk_vbind_term e then
         let hyps2, e = dest_mk_vbind_term e in
         let t_length = mk_hyps_length_term (mk_mk_vbind_term (SeqHyp.concat hyps hyps2) e) in
            t_length, hoist_hyps_length_vec
      else
         let t_length = mk_hyps_length_term (mk_mk_vbind_term hyps e) in
            t_length, hoist_hyps_length
   in

   (*
    * Define a variable of that name.
    *)
   let t_equal = mk_equal_term t_nat t_i t_length in
   let t_exists = mk_exists_term v_i t_nat t_equal in
      assertT t_exists
      thenLT [withT t_length (dT 0) ttca; dT (-1) thenT rw (addrC addr (conv t_i t_bind)) 0]

let hoistHypsLengthT = funT hoist_hyps_length_tac

(************************************************************************
 * Apply the rewrite.
 *)
let rec split_hyplist_conv hyps i t =
   if i = 0 then
      idC
   else if i = 1 then
      match SeqHyp.get hyps 0 with
         Hypothesis _ ->
            reduce_hyplist_single
       | Context _ ->
            idC
   else
      let j = pred i in
      let c =
         match SeqHyp.get hyps j with
            Hypothesis _ ->
               addrC [Subterm 2] reduce_hyplist_flatten_single
          | Context _ ->
               idC
      in
         hyplist_nest i thenC c thenC (addrC [Subterm 1] (termC (split_hyplist_conv hyps j)))

let reduce_hyplist_conv t =
   let { sequent_args = arg;
         sequent_hyps = hyps
       } = explode_sequent t
   in
      if is_hyplist_arg_term arg then
         let i = SeqHyp.length hyps in
            split_hyplist_conv hyps i t
      else
         raise (RefineError ("reduce_hyplist_conv", StringTermError ("not a hyplist term", t)))

let reduce_hyplist = termC reduce_hyplist_conv

let flatten_fsequent t =
   let hyps = (explode_sequent t).sequent_hyps in
   let i = SeqHyp.length hyps in
      unfold_fsequent thenC (addrC [Subterm 2; Subterm 1] (termC (split_hyplist_conv hyps i)))

let reduce_fsequent = termC flatten_fsequent

interactive test_intro : <:xrule<
   <H> >- fsequent{it}{| <J> >- C |} IN "top"
>>

interactive test_elim1 'J : <:xrule<
   <H> >- fsequent{it}{| <J>; x: A; <K[x]> >- C[x] |} IN "top"
>>

interactive test_elim2 'J 'K : <:xrule<
   <H> >- fsequent{it}{| <J>; x: A; <K[x]>; y: B[x]; z: C[x; y]; <L[x; y; z]> >- P[x; y] |} IN "top"
>>

(************************************************************************
 * Display forms.
 *)
dform hyplist_df : hyplist{| <H> >- 'C |} =
   szone pushm[3] `"hyplist[" display_sequent{hyplist{| <H> >- 'C |}} `"]" popm ezone

dform hyplist_hyp_df : display_hyp{hyplist; v. 'e} =
   slot{'v} `" : " slot{'e}

dform hyplist_concl_df : display_concl{hyplist; xconcl} =
   `""

dform hyplist_concl_df2 : display_concl{hyplist; 'C} =
   slot{'C}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
