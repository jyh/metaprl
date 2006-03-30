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
extends Itt_hoas_relax

doc docoff

open Lm_printf

open Basic_tactics

open Itt_list2
open Itt_equal
open Itt_struct
open Itt_squiggle
open Itt_vec_list1
open Itt_hoas_bterm
open Itt_hoas_vbind
open Itt_hoas_vector
open Itt_hoas_debruijn
open Itt_hoas_bterm_wf

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
interactive_rw length_hyplist_succ {| reduce |} : <:xrule<
   length{hyp_context{| <J> >- hyplist{| x: A; <K[x]> |} |}}
   <-->
   length{hyp_context{| <J> >- hyplist{| <K[it]> |} |}} +@ 1
>>

interactive_rw length_hyplist_right {| reduce |} : <:xrule<
   length{hyp_context{| <J> >- hyplist{| <K>; x: A |} |}}
   <-->
   length{hyp_context{| <J> >- hyplist{| <K> |} |}} +@ 1
>>

interactive_rw length_hypcontext_right {| reduce |} : <:xrule<
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
         (* XXX: reduceC does not fall back to less specific matches; have to do it manually *)
         squash_vbindC
      else
         match SeqHyp.get hyps i with
            Hypothesis (v', _) when Lm_symbol.eq v' v ->
               reduce_vbind_var (succ i)
          | Hypothesis _
          | Context _ ->
               search (succ i)
   in
      search 0

let reduce_vbind_varC = termC reduce_vbind_var_aux

let resource reduce +=
   [<< vbind{| <J> >- !x |} >>, wrap_reduce reduce_vbind_varC]

(************************************************************************
 * BTerm wf.
 *)

(*
 * Step cases.
 *)
interactive_rw vbind_eta_expand1 : <:xrewrite<
   vbind{| <J> >- bind{z. e} |}
   <-->
   bind{length{vlist{| <J> |}}; x. bind{z. substl{vbind{| <J> >- e |}; x}}}
>>

interactive_rw bindn_bind1_prefix : <:xrewrite<
   n in nat -->
   bind{n; x. bind{y. substl{e; x}}}
   <-->
   bind{n +@ 1; x. substl{e; nth_prefix{x; n}}}
>>

interactive_rw vbind_eta_expand2 : <:xrewrite<
   n in nat -->
   vbind{| <J> >- bind{n<||>; z. e} |}
   <-->
   bind{length{vlist{| <J> |}}; x. bind{n; z. substl{vbind{| <J> >- e |}; x}}}
>>

interactive vbind_bind1_wf {| intro |} : <:xrewrite<
   "wf" : <H> >- vbind{| <J> >- e |} in BTerm -->
   <H> >- vbind{| <J> >- bind{x. e} |} in BTerm
>>

interactive vbind_split_wf 'J : <:xrewrite<
   "wf" : <H> >- vbind{| <J> >- e |} in BTerm -->
   <H> >- vbind{| <J>; <K> >- e<|J,H|> |} in BTerm
>>

(*
 * Depth versions.
 *)
interactive vbind_bind1_wf2 {| intro |} : <:xrewrite<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- vbind{| <J> >- e |} in BTerm{n -@ 1} -->
   <H> >- vbind{| <J> >- bind{x. e} |} in BTerm{n}
>>

interactive vbind_split_wf2 'J : <:xrewrite<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- vbind{| <J> >- e |} in BTerm{n -@ length{hyp_context{| <J> >- hyplist{| <K> |} |}}} -->
   <H> >- vbind{| <J>; <K> >- e<|J,H|> |} in BTerm{n}
>>

(*
 * Depths.
 *)
interactive_rw reduce_bdepth_vbind_split 'J : <:xrewrite<
   vbind{| <J> >- e |} in BTerm -->
   bdepth{vbind{| <J>; <K> >- e<|J|> |}}
   <-->
   bdepth{vbind{| <J> >- e |}} +@ length{hyp_context{| <J> >- hyplist{| <K> |} |}}
>>

(*
 * Tactic.
 *)
let unused_tail t =
   let { sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in

   (* Figure out which hyps are included in the concl *)
   let vars = all_vars concl in
   let rec search i hyps =
      match hyps with
         h :: hyps ->
            (match h with
                Hypothesis (x, _)
              | Context (x, _, _) ->
                   if SymbolSet.mem vars x then
                      i
                   else
                      search (succ i) hyps)
       | [] ->
            i
   in
   let i = search 0 (List.rev (SeqHyp.to_list hyps)) in
      if i = 0 then
         raise (RefineError ("Itt_hoas_sequent_term_wf.unused_tail", StringTermError ("sequent is fully dependent", t)));
      SeqHyp.length hyps - i + 1

let vbind_split_tac p =
   let t_concl, t, _ = dest_equal (concl p) in
   let i = unused_tail t in
   let tac =
      if is_BTerm_term t_concl then
         vbind_split_wf
      else
         vbind_split_wf2
   in
      tac i

let vbind_splitT = funT vbind_split_tac

let resource intro +=
   [<:xterm< vbind{| <J> >- e |} in BTerm >>, wrap_intro vbind_splitT;
    <:xterm< vbind{| <J> >- e |} in BTerm{n} >>, wrap_intro vbind_splitT]

(*
 * Depth rewrite.
 *)
let reduce_depth_vbind_split_conv t =
   let t = dest_bdepth_term t in
   let i = unused_tail t in
      reduce_bdepth_vbind_split i

let reduce_depth_vbind_splitC = termC reduce_depth_vbind_split_conv

let resource reduce +=
   [<:xterm< bdepth{vbind{| <J> >- e |}} >>, wrap_reduce reduce_depth_vbind_splitC]

(************************************************************************
 * More splitting.
 *)
interactive_rw bind_merge_prefix : <:xrewrite<
   n in nat -->
   m in nat -->
   bind{n; x. bind{m; y. substl{e; x}}}
   <-->
   bind{n +@ m; x. substl{e; nth_prefix{x; n}}}
>>

interactive_rw vbind_split_bindn 'J : <:xrewrite<
   vbind{| <J>; <K> >- e<|J|> |}
   <-->
   vbind{| <J> >- bind{length{hyp_context{| <J> >- hyplist{| <K> |} |}}; y. e} |}
>>

interactive_rw vbind_split_prefix 'J : <:xrewrite<
   vbind{| <J>; <K> >- e<|J|> |}
   <-->
   bind{length{vlist{| <J>; <K> |}}; x. substl{vbind{| <J> >- e |}; nth_prefix{x; length{vlist{| <J> |}}}}}
>>

interactive vbind_bindn_equal 'J : <:xrewrite<
   "wf" : <H> >- m = length{vlist{| <J> |}} in nat -->
   "wf" : <H> >- n = length{vlist{| <J>; <K> |}} in nat -->
   "wf" : <H> >- vbind{| <J>; <K> >- e |} in BTerm -->
   <H> >- vbind{| <J>; <K> >- e<|J,H|> |} = bind{n; x. substl{vbind{| <J> >- e |}; nth_prefix{x; m}}} in BTerm
>>

let vbind_bindn_equal_tac p =
   let _, t1, t2 = dest_equal (concl p) in
   let tac1, t1, t2 =
      if is_vbind_term t1 then
         idT, t1, t2
      else
         equalSymT, t2, t1
   in
   let _, _, subst = dest_bindn_term t2 in
   let vbind, _ = dest_substl_term subst in
   let hyps = (explode_sequent vbind).sequent_hyps in
   let i = SeqHyp.length hyps + 1 in
      tac1 thenT vbind_bindn_equal i

let vbind_bindn_equalT = funT vbind_bindn_equal_tac

let resource intro +=
   [<:xterm< vbind{| <J> >- e1 |} = bind{n; x. substl{vbind{| <K> >- e |}; nth_prefix{x; m}}} in BTerm >>, wrap_intro vbind_bindn_equalT;
    <:xterm< bind{n; x. substl{vbind{| <K> >- e |}; nth_prefix{x; m}}} = vbind{| <J> >- e1 |} in BTerm >>, wrap_intro vbind_bindn_equalT]

(************************************************************************
 * Var properties.
 *)
interactive bind_trivial_wf {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- e in BTerm{n -@ 1} -->
   <H> >- bind{x. e} in BTerm{n}
>>

interactive vbind_var_wf {| intro |} : <:xrule<
   "wf" : <H> >- n = length{vlist{| <J> |}} +@ 1 in nat -->
   <H> >- vbind{| <J>; x: A >- x |} in BTerm{n}
>>

interactive vbind_var_wf2 {| intro |} : <:xrule<
   <H> >- vbind{| <J>; x: A >- x |} in BTerm
>>

interactive_rw reduce_depth_vbind_var {| reduce |} : <:xrewrite<
   bdepth{vbind{| <J>; x: A >- x |}}
   <-->
   length{vlist{| <J> |}} +@ 1
>>

(************************************************************************
 * Relaxed goals.
 *)
interactive hyp_depths_forward1 {| forward [ForwardPrec forward_trivial_prec] |} 'H : <:xrule<
   "wf" : <H>; x: hyp_depths{n; l}; <J[x]> >- n in nat -->
   "wf" : <H>; x: hyp_depths{n; l}; <J[x]> >- l in list{BTerm} -->
   <H>; x: hyp_depths{n; l}; <J[x]>; l in list{Bind{n}} >- C[x] -->
   <H>; x: hyp_depths{n; l}; <J[x]> >- C[x]
>>

(************************************************************************
 * More depth lemmas.
 *)
let resource forward_subst +=
   [<:xterm< bdepth{vbind{| <J> >- e1 |}} = length{e2} in nat >>, ()]

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
