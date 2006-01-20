doc <:doc<
   @module[Itt_vec_list1]

   The @tt[Itt_vec_list1] module defines lists expressed as
   sequents.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998-2005 MetaPRL Group, Caltech

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
extends Meta_context_theory
extends Itt_theory
extends Itt_vec_dform
extends Itt_list3

doc docoff

open Lm_printf
open Basic_tactics
open Simple_print

open Base_trivial
open Itt_equal
open Itt_list2
open Itt_list

(************************************************************************
 * Vlist.
 *)

(*
 * BUG: Unfortunately, we don't have define forms for sequents.
 * Temporarily use the declare/prim_rw form.
 *)
doc <:doc<
   The vector list produces a list from the hyps.
>>
declare sequent [vlist_nest] { Term : Term >- Term } : Term

prim_rw unfold_vlist_nest : vlist_nest{| <H> >- 'C |} <-->
   sequent_ind{u, v. cons{'u; happly{'v; it}}; SequentTerm{| <H> >- 'C |}}

doc <:doc<
   Reductions.
>>
interactive_rw reduce_vlist_nest_nil {| reduce |} :
   vlist_nest{| >- 'l |}
   <-->
   'l

interactive_rw reduce_vlist_nest_left :
   vlist_nest{| y: 'e; <J['y]> >- 'l['y] |}
   <-->
   cons{'e; vlist_nest{| <J[it]> >- 'l[it] |}}

interactive_rw reduce_vlist_nest_right :
   vlist_nest{| <J>; x: 'e >- 'l['x] |}
   <-->
   vlist_nest{| <J> >- cons{'e; 'l[it]} |}

interactive_rw hoist_vlist_nest_concl :
   vlist_nest{| <J> >- cons{'e; 'l} |}
   <-->
   vlist_nest{| <J>; 'e >- 'l |}

interactive_rw reduce_vlist_nest_bind_right :
   vlist_nest{| <J>; x: 'e >- 'l['x] |}
   <-->
   vlist_nest{| <J>; 'e >- 'l[it] |}

interactive_rw reduce_vlist_nest_split 'J :
   vlist_nest{| <J>; <K> >- 'l |}
   <-->
   vlist_nest{| <J> >- vlist_nest{| <K> >- 'l |} |}

doc <:doc<
   Well-formedness for the nested version of vector lists.
>>
interactive vlist_nest_concl_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in list{'A} } -->
   sequent { <H> >- vlist_nest{| >- 'l |} in list{'A} }

interactive vlist_nest_left_wf {| intro [] |} :
   [wf] sequent { <H> >- 'e in 'A } -->
   [wf] sequent { <H> >- vlist_nest{| <J[it]> >- 'l[it] |} in list{'A} } -->
   sequent { <H> >- vlist_nest{| x: 'e; <J['x]> >- 'l['x] |} in list{'A} }

doc <:doc<
   The actual << vlist{| <J> |} >> ignores its conclusion.
>>
declare sequent [vlist] { Term : Term >- Term } : Term

prim_rw unfold_vlist : vlist{| <J> >- 'C |} <-->
   vlist_nest{| <J> >- nil |}

interactive_rw reduce_vlist_nil {| reduce |} :
   vlist{||}
   <-->
   nil

interactive_rw reduce_vlist_left :
   vlist{| x: 'A; <J['x]> |}
   <-->
   'A :: vlist{| <J[it]> |}

interactive_rw reduce_vlist_split 'J :
   vlist{| <J>; <K<||> > |}
   <-->
   append{vlist{| <J> |}; vlist{| <K> |}}

interactive vlist_nil_wf :
   [wf] sequent { <H> >- 'A Type } -->
   sequent { <H> >- vlist{||} in list{'A} }

interactive vlist_left_wf :
   [wf] sequent { <H> >- 'e in 'A } -->
   [wf] sequent { <H> >- vlist{| <J[it]> |} in list{'A} } -->
   sequent { <H> >- vlist{| x: 'e; <J['x]> |} in list{'A} }

interactive vlist_split_wf 'J :
   [wf] sequent { <H> >- vlist{| <J> |} in list{'A} } -->
   [wf] sequent { <H> >- vlist{| <K> |} in list{'A} } -->
   sequent { <H> >- vlist{| <J>; <K<|H|> > |} in list{'A} }

doc docoff

(*
 * Define a tactic for the case analysis on vlist.
 *)
let vlist_wf_tac p =
   let t = concl p in
   let _, t1, _ = dest_equal t in
   let hyps = (explode_sequent t1).sequent_hyps in
   let len = SeqHyp.length hyps in
      if len = 0 then
         vlist_nil_wf
      else
         match SeqHyp.get hyps 0 with
            Hypothesis _ ->
               vlist_left_wf
          | Context _ ->
               vlist_split_wf 2

let resource intro +=
   [<< vlist{| <J> |} in list{'A} >>, wrap_intro (funT vlist_wf_tac)]

doc <:doc<
   A vlist is @emph{always} a list.
>>
interactive vlist_wf {| intro [] |} :
   sequent { <H> >- vlist{| <J> |} in list }

doc <:doc<
   The @refmodule[Itt_list2] module defines a conditional rewrite
   << 'l in list => 'l ~ list_of_fun{i. nth{'l; 'i}; length{'l}} >>.
   Define an equivalent form that is unconditional.
>>
interactive_rw vlist_of_nil :
   nil
   <-->
   vlist{||}

interactive_rw expand_vlist_left :
   'A :: vlist{| <J> |}
   <-->
   vlist{| 'A; <J> |}

interactive_rw list_of_fun_of_vlist :
   vlist{| <J> |}
   <-->
   list_of_fun{i. nth{vlist{| <J> |}; 'i}; length{vlist{| <J> |}}}

interactive_rw list_of_fun_of_vlist_elem :
   vlist{| <J> |}
   <-->
   list_of_fun{i. nth{vlist{| <J> |}; 'i}; length{vlist{| <J> |}}}

(************************************************************************
 * Squash list.
 *)
doc <:doc<
   The << vsquashlist{| <J> >- 'l |} >> is the list where all hyps are
   replaced by the term << it >>.  Most commonly, the << vsquashlist{| <J> >- 'l |} >>
   term is used in << length{'e} >> reasoning, where the elements don't matter.
>>
declare sequent [vsquashlist] { Term : Term >- Term } : Term

prim_rw unfold_vsquashlist :
   vsquashlist{| <J> >- 'l |}
   <-->
   sequent_ind{u, v. it :: happly{'v; it}; TermSequent{| <J> >- 'l |}}

interactive_rw reduce_vsquashlist_concl {| reduce |} :
   vsquashlist{| >- 'l |}
   <-->
   'l

interactive_rw reduce_vsquashlist_left :
   vsquashlist{| x: 'A; <J['x]> >- 'l['x] |}
   <-->
   it :: vsquashlist{| <J[it]> >- 'l[it] |}

interactive_rw reduce_vsquashlist_right :
   vsquashlist{| <J>; x : 'A >- 'l['x] |}
   <-->
   vsquashlist{| <J> >- it :: 'l[it] |}

doc <:doc<
   The length of a list does not depend on the elements.
>>
interactive_rw reduce_length_of_vlist :
   length{vlist{| <J> |}}
   <-->
   length{vsquashlist{| <J> >- nil |}}

doc <:doc<
   This is the primary hoisting theorem, where we show that the length
   of the list does not depend on any free variables.
>>
interactive_rw reduce_length_fun :
   lambda{x. length{vlist{| <J['x]> |}}}
   <-->
   lambda{x. length{vlist{| <J[it]> |}}}

interactive_rw reduce_length_fun_term Perv!bind{x. length{vlist{| <J['x]> |}}} :
   length{vlist{| <J['x]> |}}
   <-->
   length{vlist{| <J[it]> |}}

(* Auxiliary goal *)
let assert_reduce_length_of_fun_term1 = <<
   all l: list{unit}.
   lambda{x. length{vsquashlist{| <J['x]> >- 'l |}}}
   ~
   lambda{x. lambda{x. length{vsquashlist{| <J['x]> >- 'l |}}} it}
>>

doc <:doc<
   Length reductions.
>>
interactive_rw reduce_length_vlist_nil {| reduce |} : <:xrewrite<
   length{vlist{||}}
   <-->
   0
>>

interactive_rw reduce_length_vlist_left : <:xrewrite<
   length{vlist{| A; <J> |}}
   <-->
   length{vlist{| <J> |}} +@ 1
>>

interactive_rw reduce_length_vlist_right : <:xrewrite<
   length{vlist{| <J>; A |}}
   <-->
   length{vlist{| <J> |}} +@ 1
>>

interactive_rw reduce_length_vlist_append 'J : <:xrewrite<
   length{vlist{| <J>; <K<||> > |}}
   <-->
   length{vlist{| <J> |}} +@ length{vlist{| <K> |}}
>>

(************************************************************************
 * Flattening.
 *)
doc <:doc<
   The << flatten{'l} >> term flattens a list using << append{'l1; 'l2} >>.
>>
define unfold_flatten : flatten{'l} <-->
   list_ind{'l; nil; u, v, g. append{'u; 'g}}

interactive_rw reduce_flatten_nil {| reduce |} :
   flatten{nil}
   <-->
   nil

interactive_rw reduce_flatten_cons {| reduce |} :
   flatten{'u::'v}
   <-->
   append{'u; flatten{'v}}

interactive flatten_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in list{list} } -->
   sequent { <H> >- flatten{'l} in list }

doc <:doc<
   The << vflatten_nest{| <J> >- 'l |} >> term provides a sequent version of
   flattening.
>>
declare sequent [vflatten_nest] { Term : Term >- Term } : Term

prim_rw unfold_vflatten_nest : vflatten_nest{| <J> >- 'C |} <-->
   sequent_ind{u, v. append{'u; happly{'v; it}}; TermSequent{| <J> >- 'C |}}

interactive_rw reduce_vflatten_nest_nil {| reduce |} :
   vflatten_nest{| >- 'C |}
   <-->
   'C

interactive_rw reduce_vflatten_nest_left :
   vflatten_nest{| x: 'A; <J['x]> >- 'C['x] |}
   <-->
   append{'A; vflatten_nest{| <J[it]> >- 'C[it] |}}

interactive_rw reduce_vflatten_nest_right :
   vflatten_nest{| <J>; x: 'A >- 'C['x] |}
   <-->
   vflatten_nest{| <J> >- append{'A; 'C[it]} |}

interactive_rw reduce_vflatten_nest_split 'J :
   vflatten_nest{| <J>; <K> >- 'C |}
   <-->
   vflatten_nest{| <J> >- vflatten_nest{| <K> >- 'C |} |}

doc <:doc<
   The << vflatten{| <J> |} >> term ignores the conclusion.
>>
declare sequent [vflatten] { Term : Term >- Term } : Term

prim_rw unfold_vflatten : vflatten{| <J> >- 'C |} <-->
   vflatten_nest{| <J> >- nil |}

interactive_rw reduce_vflatten_nil {| reduce |} :
   vflatten{||}
   <-->
   nil

interactive_rw reduce_vflatten_singleton {| reduce |} :
   vflatten{| cons{'e; nil} |}
   <-->
   cons{'e; nil}

interactive_rw reduce_vflatten_left :
   vflatten{| x: 'A; <J['x]> |}
   <-->
   append{'A; vflatten{| <J[it]> |}}

doc <:doc<
   Well-formedness reasoning.
>>
interactive vflatten_list_wf {| intro [] |} :
   [wf] sequent { <H> >- vlist{| <J> |} in list{list} } -->
   sequent { <H> >- vflatten{| <J> |} in list }

doc <:doc<
   Associative properties.
>>
interactive_rw reduce_vflatten_split 'J :
   vlist{| <J> |} in list{list} -->
   vflatten{| <J>; <K<||> > |}
   <-->
   append{vflatten{| <J> |}; vflatten{| <K> |}}

interactive_rw vflatten_collect 'J 'K :
   vlist{| <J> |} in list{list} -->
   vlist{| <K> |} in list{list} -->
   vflatten{| <J>; <K<||> >; <L<||> > |}
   <-->
   vflatten{| <J>; vflatten{| <K> |}; <L> |}

interactive_rw vflatten_flatten 'J :
   vlist{| <J> |} in list{list} -->
   vlist{| <K> |} in list{list} -->
   vflatten{| <J>; vflatten{| <K<||> > |}; <L<||> > |}
   <-->
   vflatten{| <J>; <K>; <L> |}

doc <:doc<
   Forming flatten vectors out of nested appends.
>>
interactive_rw vflatten_of_append :
   'l1 in list -->
   'l2 in list -->
   append{'l1; 'l2}
   <-->
   vflatten{| 'l1; 'l2 |}

interactive_rw reduce_vflatten_append 'J :
   'l1 in "list" -->
   'l2 in "list" -->
   vflatten{| <J>; x: append{'l1<||>; 'l2<||>}; <K['x]> |}
   <-->
   vflatten{| <J>; 'l1; 'l2; <K[it]> |}

doc <:doc<
   Length reductions.
>>
interactive_rw length_of_vflatten_nil {| reduce |} :
   length{vflatten{||}}
   <-->
   0

interactive_rw length_of_vflatten_cons {| reduce |} :
   'l in list -->
   vlist{| <J> |} in list{list} -->
   length{vflatten{| 'l; <J> |}}
   <-->
   length{'l} +@ length{vflatten{| <J> |}}

(*
 * XXX: BUG!!! Meta_context_terms.reduce_sequent_ind_base1 is too strong.
 *)
interactive_rw bug : 0 <--> 1

(************************************************************************
 * Display forms.
 *)
doc docoff

dform vlist_nest_df : vlist_nest{| <H> |} =
   szone pushm[1] `"[" display_sequent{vlist_nest{| <H> |}} `"]" popm ezone

dform vlist_nest_hyp_df : display_hyp{vlist_nest; x. 'e} =
   szone pushm[3] slot{'x} `":" hspace slot{'e} popm ezone

dform vlist_nest_sep_df : display_hyp_sep{vlist_nest} =
   `";" hspace

dform vlist_nest_concl_df : display_concl{vlist_nest; 'c} =
   `"???"

dform vlist_nest_concl_df : display_concl{vlist_nest; xconcl} =
   `""

(************************************************************************
 * Tactics.
 *)
let fold_vlist_nest = makeFoldC << vlist_nest{| <H> >- 'C |} >> unfold_vlist_nest
let fold_vflatten_nest = makeFoldC << vflatten_nest{| <J> >- 'C |} >> unfold_vflatten_nest

let var_x = Lm_symbol.add "x"

(*
 * Squash vlist{| <J[x]> |} terms to vlist{| <J[it]> |}.
 *)
let reduce_length_fun_term_conv t =
   let s = dest_length t in

   (*
    * Find the term to be replaced.
    *)
   let hyps = (explode_sequent s).sequent_hyps in
   let len = SeqHyp.length hyps in
   let rec search i =
      if i = len then
         raise (RefineError ("reduce_length_fun_term_conv", StringTermError ("already converted", t)))
      else
         match SeqHyp.get hyps i with
            Context (_, _, args) ->
               let rec search_args args =
                  match args with
                     arg :: args ->
                        if is_it_term arg then
                           search_args args
                        else
                           arg
                   | [] ->
                        search (succ i)
               in
                  search_args args
          | _ ->
               search (succ i)
   in
   let v_term = search 0 in

   (*
    * Make a new variable, and replace the subterm.
    *)
   let x = maybe_new_var_set var_x (free_vars_set t) in
   let t_var = var_subst t v_term x in
   let t_bind = mk_bind1_term x t_var in
      reduce_length_fun_term t_bind

(*
 * Split the << length{vlist{| <J> |}} >> into a sum.
 *)
let rec reduce_length_vlist_term t =
   let s = dest_length t in
   let hyps = (explode_sequent s).sequent_hyps in
   let len = SeqHyp.length hyps in
      if SeqHyp.length hyps = 0 then
         reduce_length_vlist_nil
      else
         match SeqHyp.get hyps 0 with
            Hypothesis _ ->
               reduce_length_vlist_left
               thenC addrC [Subterm 1] (termC reduce_length_vlist_term)
          | Context _ ->
               if len = 1 then
                  idC
               else
                  reduce_length_vlist_append 2
                  thenC addrC [Subterm 2] (termC reduce_length_vlist_term)

let reduce_length_fun_termC =
   repeatC (termC reduce_length_fun_term_conv)
   thenC termC reduce_length_vlist_term

let resource reduce +=
   [<< length{vlist{| <J> |}} >>, wrap_reduce reduce_length_fun_termC]

doc <:doc<
   The @tt[vlist_of_concrete_listC] conversion collects the elements
   of a concrete list into a << vlist{| <J> |} >>.

   @docoff
>>
let rec find_nil_rev_address addr t =
   if is_cons_term t then
      let _, t = dest_cons t in
      let addr = Subterm 2 :: addr in
         find_nil_rev_address addr t
   else if is_nil_term t then
      addr
   else
      raise (RefineError ("find_nil_rev_address", StringTermError ("not a list term", t)))

let vlist_of_concrete_list t =
   let raddr = find_nil_rev_address [] t in
   let rec foldC raddr =
      match raddr with
         [] ->
            idC
       | _ :: rest ->
            addrC (List.rev rest) expand_vlist_left thenC foldC rest
   in
      addrC raddr vlist_of_nil thenC foldC raddr

let vlist_of_concrete_listC = termC vlist_of_concrete_list

(************************************************************************
 * Display forms.
 *)
dform vlist_df : vlist{| <H> >- 'C |} =
   szone pushm[3] `"vlist[" display_sequent{vlist{| <H> >- 'C |}} `"]" popm ezone

dform vlist_hyp_df : display_hyp{vlist; v. 'e} =
   slot{'e}

dform vlist_concl_df : display_concl{vlist; xconcl} =
   `""

dform vlist_concl_df2 : display_concl{vlist; 'C} =
   slot{'C}

dform vflatten_df : vflatten{| <H> >- 'C |} =
   szone pushm[3] `"vflatten[" display_sequent{vflatten{| <H> >- 'C |}} `"]" popm ezone

dform vflatten_hyp_df : display_hyp{vflatten; v. 'e} =
   slot{'e}

dform vflatten_concl_df : display_concl{vflatten; xconcl} =
   `""

dform vflatten_concl_df2 : display_concl{vflatten; 'C} =
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
