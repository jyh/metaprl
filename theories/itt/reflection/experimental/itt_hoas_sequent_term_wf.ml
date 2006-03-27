doc <:doc<
   @module[Itt_hoas_sequent_term_wf]

   Additional rewrites and rules used for proving well-formedness
   of sequent terms.

   @begin[license]
   Copyright (C) 2005-2006 Mojave Group, Caltech

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
extends Itt_hoas_sequent_term
extends Itt_hoas_normalize
extends Itt_hoas_bterm_wf

doc docoff

open Basic_tactics

open Itt_list2
open Itt_vec_list1

(************************************************************************
 * Length reductions.
 *)
interactive_rw reduce_length_vlist_single {| reduce |} : <:xrewrite<
   length{vlist{| A |}}
   <-->
   1
>>

interactive_rw reduce_length_vlist_hyp : <:xrewrite<
   length{vlist{| <J>; x: A |}}
   <-->
   length{vlist{| <J> |}} +@ 1
>>

interactive_rw reduce_length_vlist_context 'J : <:xrewrite<
   length{vlist{| <J>; <K> |}}
   <-->
   length{vlist{| <J> |}} +@ length{hyp_context{| <J> >- hyplist{| <K> |} |}}
>>

let rec reduce_length_vlist_hyps len hyps =
   match hyps with
      h :: hyps ->
         let c =
            match h with
               Hypothesis _ ->
                  reduce_length_vlist_hyp
             | Context _ ->
                  reduce_length_vlist_context len
         in
            c thenC addrC [Subterm 1] (reduce_length_vlist_hyps (pred len) hyps)
    | [] ->
         idC

let reduce_length_vlist_aux t =
   let t = dest_length t in
   let hyps = (explode_sequent t).sequent_hyps in
   let len = SeqHyp.length hyps in
      if len = 0 then
         addrC [Subterm 1] reduce_vlist_nil
         thenC reduce_length_nil
      else if len = 1 then
         raise (RefineError ("reduce_length_vlist_aux", StringTermError ("already reduced", t)))
      else
         reduce_length_vlist_hyps len (List.rev (List.tl (SeqHyp.to_list hyps)))

let reduce_length_vlistC = termC reduce_length_vlist_aux

let resource reduce +=
   [<< length{vlist{| <J> |}} >>, wrap_reduce reduce_length_vlistC]

(************************************************************************
 * More squashing.
 *)
interactive_rw squash_hyp_context_bind 'J : <:xrewrite<
   length{hyp_context{| <J>; x: A; <K[x]> >- hyplist{| <L[x]> |} |}}
   <-->
   length{hyp_context{| <J>; x: A; <K[x]> >- hyplist{| <L[it]> |} |}}
>>

let squash_hyp_context_bind_aux t =
   let t = dest_length t in
   let hyps = (explode_sequent t).sequent_hyps in
   let convs, _ =
      List.fold_left (fun (convs, i) h ->
            let convs =
               match h with
                  Hypothesis _ ->
                     squash_hyp_context_bind i :: convs
                | Context _ ->
                     convs
            in
               convs, succ i) ([], 1) (SeqHyp.to_list hyps)
   in
      match convs with
         [] ->
            raise (RefineError ("squash_hyp_context_bind_aux", StringTermError ("already squashed", t)))
       | c :: cl ->
            let c =
               List.fold_left (fun c1 c2 ->
                     c2 thenC c1) c cl
            in
               progressC c

let squash_hyp_context_bindC = termC squash_hyp_context_bind_aux

let resource reduce +=
   [<< length{hyp_context{| <J> >- hyplist{| <K> |} |}} >>, wrap_reduce squash_hyp_context_bindC]

(************************************************************************
 * Vbinds.
 *)
interactive_rw length_hyplist_succ : <:xrule<
   length{hyp_context{| <J> >- hyplist{| x: A; <K[x]> |} |}}
   <-->
   length{hyp_context{| <J> >- hyplist{| <K[it]> |} |}} +@ 1
>>

interactive_rw length_hypcontext_right : <:xrule<
   length{hyp_context{| <J>; x: A >- hyplist{| <K[x]> |} |}}
   <-->
   length{hyp_context{| <J> >- hyplist{| <K[it]> |} |}}
>>

interactive_rw vbind_of_bind_trivial : <:xrule<
   bind{length{vlist{| <J> |}}; x. e}
   <-->
   vbind{| <J> >- e |}
>>

interactive_rw reduce_bindn_vbind_up : <:xrewrite<
   bind{length{vlist{| <J> |}} +@ 1; x. e[x]}
   <-->
   bind{x. bind{length{vlist{| <J> |}}; y. e[x :: y]}}
>>

interactive_rw length_hyplist_assoc : <:xrewrite<
   j in nat -->
   k in nat -->
   (length{hyp_context{| <J> >- hyplist{| <K> |} |}} +@ j) +@ k
   <-->
   length{hyp_context{| <J> >- hyplist{| <K> |} |}} +@ (j +@ k)
>>

interactive_rw length_vlist_zero : <:xrewrite<
   length{vlist{| <J> |}} +@ 0
   <-->
   length{vlist{| <J> |}}
>>

interactive_rw length_hyp_context_zero : <:xrewrite<
   length{hyp_context{| <J> >- hyplist{| <K> |} |}} +@ 0
   <-->
   length{hyp_context{| <J> >- hyplist{| <K> |} |}}
>>

interactive_rw split_vbind_trivial 'J : <:xrewrite<
   vbind{| <J>; <K> >- e<|J|> |}
   <-->
   vbind{| <J> >- bind{length{hyp_context{| <J> >- hyplist{| <K> |} |}}; x. e} |}
>>

interactive_rw reduce_vbind_var 'J : <:xrule<
   vbind{| <J>; x: A; <K[x]> >- 'x |}
   <-->
   var{length{vlist{| <J> |}}; length{hyp_context{| <J>; x: 'A >- hyplist{| <K[x]> |} |}}}
>>

let reduce_vbind_var_aux t =
   let { sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in
   let v = dest_var concl in
   let len = SeqHyp.length hyps in
   let rec search i =
      if i = len then
         raise (RefineError ("reduce_vbind_var_aux", StringTermError ("not a variable", t)));
      match SeqHyp.get hyps i with
         Hypothesis (v', _) when Lm_symbol.eq v' v ->
            succ i
       | Hypothesis _
       | Context _ ->
            search (succ i)
   in
      reduce_vbind_var (search 0)

let reduce_vbind_varC = termC reduce_vbind_var_aux

let resource reduce +=
   [<< vbind{| <J> >- 'x |} >>, wrap_reduce reduce_vbind_varC]

(************************************************************************
 * Depths.
 *)
interactive_rw reduce_depth_vbind_trivial {| reduce |} : <:xrewrite<
   e in BTerm -->
   bdepth{vbind{| <J> >- e<||> |}}
   <-->
   length{vlist{| <J> |}} +@ bdepth{e}
>>

(************************************************************************
 * BTerm wf.
 *)
interactive vbind_trivial_wf {| intro |} : <:xrewrite<
   "wf" : <H> >- e in BTerm -->
   <H> >- vbind{| <J> >- e<|H|> |} in BTerm
>>

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
