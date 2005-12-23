doc <:doc<
   @module[Itt_hoas_bterm_wf]
   The @tt[Itt_hoas_bterm_wf] module defines additional well-formedness
   rules for BTerms.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2005, MetaPRL Group

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
extends Itt_hoas_bterm
extends Itt_hoas_util
extends Itt_vec_list1
extends Itt_vec_bind
extends Itt_list3

doc docoff

open Lm_printf
open Basic_tactics
open Itt_vec_list1
open Itt_hoas_base
open Itt_hoas_vector
open Itt_hoas_debruijn
open Itt_equal

(************************************************************************
 * Subterm bind lists.
 *)
doc <:doc<
   The term << subterms_bind{'e} >> transforms a binding around a list
   << bind{x. cons{'e1['x]; math_ldots}} >> to a list of
   binds << cons{bind{x. 'e1['x]}; math_ldots} >>.
>>
define unfold_subterms_length : subterms_length{'e} <--> <:xterm<
   (fix f e -> weak_dest_terms{e; f subst{e; "it"}; l. length{l}}) e
>>

define unfold_subterms_nth : subterms_nth{'e; 'i} <--> <:xterm<
   (fix f e -> weak_dest_terms{e; bind{x. f subst{e; x}}; l. nth{l; i}}) e
>>

define unfold_subterms_bind : subterms_bind{'e} <--> <:xterm<
   list_of_fun{k. subterms_nth{e; k}; subterms_length{e}}
>>

doc docoff

let fold_subterms_length = makeFoldC << subterms_length{'e} >> unfold_subterms_length
let fold_subterms_nth = makeFoldC << subterms_nth{'e; 'i} >> unfold_subterms_nth
let fold_subterms_bind = makeFoldC << subterms_bind{'e} >> unfold_subterms_bind

(************************************************
 * Term reductions.
 *)
interactive_rw reduce_subterms_bind {| reduce |} : <:xrewrite<
   subterms_length{bind{x. e[x]}}
   <-->
   subterms_length{e["it"]}
>>

interactive_rw reduce_subterms_terms {| reduce |} : <:xrewrite<
   subterms_length{mk_terms{e}}
   <-->
   length{e}
>>

interactive_rw reduce_subterms_bindn {| reduce |} : <:xrewrite<
   n IN "nat" -->
   subterms_length{bind{n; x. mk_terms{"vlist"{| <J[x]> |}}}}
   <-->
   length{"vlist"{| <J["it"]> |}}
>>

interactive_rw reduce_subterms_nth_bind {| reduce |} : <:xrewrite<
   subterms_nth{bind{x. e[x]}; i}
   <-->
   bind{x. subterms_nth{e[x]; i}}
>>

interactive_rw reduce_subterms_nth_bindn {| reduce |} : <:xrewrite<
   n IN "nat" -->
   subterms_nth{bind{n; x. e[x]}; i}
   <-->
   bind{n; x. subterms_nth{e[x]; i}}
>>

interactive_rw reduce_subterms_nth_mk_terms {| reduce |} : <:xrewrite<
   subterms_nth{mk_terms{e}; i}
   <-->
   nth{e; i}
>>

(************************************************
 * Step-by-step reductions.
 *)
doc <:doc<
   For concrete << subterms_bind{bind{x. mk_terms{vlist{| 'e_1['x]; math_ldots; 'e_n['x] |}}}} >>,
   define a step-by-step reduction.
>>
interactive_rw reduce_subterms_bind1_nil {| reduce |} : <:xrewrite<
   subterms_bind{bind{x. mk_terms{"vlist"{||}}}}
   <-->
   []
>>

interactive_rw reduce_subterms_bind1_cons {| reduce |} : <:xrewrite<
   subterms_bind{bind{x. mk_terms{"vlist"{| A[x]; <J[x]> |}}}}
   <-->
   bind{x. A[x]} :: subterms_bind{bind{x. mk_terms{"vlist"{| <J[x]> |}}}}
>>

interactive_rw reduce_subterms_bindn_nil {| reduce |} : <:xrewrite<
   n IN "nat" -->
   subterms_bind{bind{n; x. mk_terms{"vlist"{||}}}}
   <-->
   []
>>

interactive_rw reduce_subterms_bindn_cons {| reduce |} : <:xrewrite<
   n IN "nat" -->
   subterms_bind{bind{n; x. mk_terms{"vlist"{| A[x]; <J[x]> |}}}}
   <-->
   bind{n; x. A[x]} :: subterms_bind{bind{n; x. mk_terms{"vlist"{| <J[x]> |}}}}
>>

doc docoff

let rec reduce_subterms_bind1 t =
   (reduce_subterms_bind1_cons
    thenC addrC [Subterm 2] (termC reduce_subterms_bind1))
   orelseC reduce_subterms_bind1_nil

let rec reduce_subterms_bindn t =
   (reduce_subterms_bindn_cons
    thenC addrC [Subterm 2] (termC reduce_subterms_bindn))
   orelseC reduce_subterms_bindn_nil

(************************************************************************
 * The bind pushing theorems.
 *)
interactive_rw reduce_list_of_fun_of_bind_vlist {| reduce |} :
   list_of_fun{i. bind{x. nth{vlist{| <J['x]> |}; 'i}}; length{vlist{| <J[it]> |}}}
   <-->
   subterms_bind{bind{x. mk_terms{vlist{| <J['x]> |}}}}

interactive_rw reduce_list_of_fun_of_bindn_vlist {| reduce |} :
   'n in nat -->
   list_of_fun{i. bind{'n; x. nth{vlist{| <J['x]> |}; 'i}}; length{vlist{| <J[it]> |}}}
   <-->
   subterms_bind{bind{'n; x. mk_terms{vlist{| <J['x]> |}}}}

interactive_rw reduce_bind_of_mk_bterm :
   'n in nat -->
   bind{x. mk_bterm{'n; 'op; vlist{| <J['x]> |}}}
   <-->
   mk_bterm{'n +@ 1; 'op; subterms_bind{bind{x. mk_terms{vlist{| <J['x]> |}}}}}

interactive_rw reduce_bindn_of_mk_bterm :
   'i in nat -->
   'n in nat -->
   bind{'i; x. mk_bterm{'n; 'op; vlist{| <J['x]> |}}}
   <-->
   mk_bterm{'n +@ 'i; 'op; subterms_bind{bind{'i; x. mk_terms{vlist{| <J['x]> |}}}}}

(************************************************************************
 * Tactics.
 *)
doc <:doc<
   Define a tactic for wf proofs.
   The main goal here is to reduce the outer binds.
   That is, if we have a goal of the form
@begin[verbatim]
    <H> >- bind{'n; x. mk_bterm{'m; 'op; 'subterms['x]}}}
@end[verbatim]
   then we want to push the bind into the term, and compute
   well-formedness from there.
>>
let reduce_bind_term t =
   (* Figure out the shape of the term *)
   let mk_term_flag, bindn_flag =
      if is_bind_term t then
         let v, t = dest_bind_term t in
         let mk_term_flag =
            if is_mk_term_term t then
               true
            else if is_mk_bterm_term t then
               false
            else
               raise (RefineError ("reduce_push_bind", StringTermError ("not a mk_[b]term", t)))
         in
            mk_term_flag, false
      else if is_bindn_term t then
         let n, v, t = dest_bindn_term t in
         let mk_term_flag =
            if is_mk_term_term t then
               true
            else if is_mk_bterm_term t then
               false
            else
               raise (RefineError ("reduce_push_bind", StringTermError ("not a mk_[b]term", t)))
         in
            mk_term_flag, true
      else
         raise (RefineError ("reduce_push_bind", StringTermError ("not a bind term", t)))
   in

   (* Address of the mk_[b]term part *)
   let term_addr =
      if bindn_flag then
         2
      else
         1
   in

   (* Turn the mk_term into a mk_bterm *)
   let fold_mk_termC =
      if mk_term_flag then
         addrC [Subterm term_addr] fold_mk_term
      else
         idC
   in

   (* The reduction rule *)
   let reduce_bindC, reduce_subterms_bindC =
      if bindn_flag then
         reduce_bindn_of_mk_bterm, termC reduce_subterms_bindn
      else
         reduce_bind_of_mk_bterm, termC reduce_subterms_bind1
   in
      (* Transform to a vlist *)
      fold_mk_termC
      thenC addrC [Subterm term_addr; Subterm 3] vlist_of_concrete_listC
      thenC reduce_bindC
      thenC addrC [Subterm 3] (repeatC reduce_subterms_bindC)

(*
 * Push all the binds.
 *)
let rec find_mk_term_rev_address raddr t =
   if is_mk_term_term t || is_mk_bterm_term t then
      raddr
   else if Itt_hoas_base.is_bind_term t then
      let _, t = Itt_hoas_base.dest_bind_term t in
      let raddr = Subterm 1 :: raddr in
         find_mk_term_rev_address raddr t
   else if is_bindn_term t then
      let _, _, t = dest_bindn_term t in
      let raddr = Subterm 2 :: raddr in
         find_mk_term_rev_address raddr t
   else
      raise (RefineError ("find_mk_term_rev_address", StringTermError ("not a bind term", t)))

let reduce_bind_term_conv t =
   let rec foldC raddr =
      match raddr with
         [] ->
            idC
       | _ :: rest ->
            addrC (List.rev rest) (termC reduce_bind_term) thenC foldC rest
   in
   let addr = find_mk_term_rev_address [] t in
      foldC addr

let reduceBindTermC = termC reduce_bind_term_conv

(*
 * Define the tactic.
 *)
let rec is_bind_mk_term t =
   if Itt_hoas_base.is_bind_term t then
      let _, t = Itt_hoas_base.dest_bind_term t in
         is_bind_mk_term t
   else if is_bindn_term t then
      let _, _, t = dest_bindn_term t in
         is_bind_mk_term t
   else
      is_mk_term_term t || is_mk_bterm_term t

let bind_wf p =
   let t = concl p in
      if is_equal_term t then
         let _, t1, t2 = dest_equal t in
            if is_bind_mk_term t1 && is_bind_mk_term t2 then
               rw (addrC [Subterm 2] reduceBindTermC thenC addrC [Subterm 3] reduceBindTermC) 0
               thenT dT 0
            else
               raise (RefineError ("bind_wf", StringTermError ("not a bterm equality", t)))
      else
         raise (RefineError ("bind_wf", StringTermError ("not a bterm equality", t)))

let bindWFT = funT bind_wf

let bind_wf = wrap_intro bindWFT

let resource intro +=
   [<< bind{x. 'e['x]} in BTerm >>, bind_wf;
    << bind{'n; x. 'e['x]} in BTerm >>, bind_wf;
    << bind{x. 'e['x]} in BTerm{'m} >>, bind_wf;
    << bind{'n; x. 'e['x]} in BTerm{'m} >>, bind_wf]

(*
 * Reduce a depth term.
 *)
let reduce_depth_termC =
   addrC [Subterm 1] reduceBindTermC thenC reduce_bdepth_mk_bterm

let resource reduce +=
   [<< bdepth{bind{'n; x. 'e['x]}} >>, reduce_depth_termC]

let proofRuleWFT =
   repeatT (autoT thenT tryT bindWFT thenT rw reduceC 0)

(************************************************************************
 * Depth wf.
 *)
interactive_rw reduce_bind_of_bterm2 BTerm{'d} : <:xrewrite<
   e IN BTerm{d} -->
   bdepth{e}
   <-->
   d
>>

let reduce_depth_of_exp e =
   let t = env_term e in
   let t = dest_bdepth_term t in
   let p = env_arg e in
   let ty =
      try get_with_arg p with
         RefineError _ ->
            infer_type p t
   in
      reduce_bind_of_bterm2 ty

let reduceDepthBTerm2C = funC reduce_depth_of_exp

let resource reduce +=
   [<< bdepth{'e} >>, reduceDepthBTerm2C]

(************************************************************************
 * Bind coalescing.
 *)
interactive_rw coalesce_bind_bind {| reduce |} : <:xrewrite<
   bind{x. bind{y. e[x; y]}}
   <-->
   bind{2; x. e[nth{x; 0}; nth{x; 1}]}
>>

interactive_rw coalesce_bind_bindn : <:xrewrite<
   n IN "nat" -->
   bind{y. bind{n; x. e[y; x]}}
   <-->
   bind{n +@ 1; x. e[hd{x}; tl{x}]}
>>

interactive_rw coalesce_bindn_bind : <:xrewrite<
   n IN "nat" -->
   bind{n; x. bind{y. e[x; y]}}
   <-->
   bind{n +@ 1; x. e[nth_prefix{x; n}; nth{x; n}]}
>>

interactive_rw coalesce_bindn_bindn : <:xrewrite<
   n IN "nat" -->
   m IN "nat" -->
   bind{n; x. bind{m; y. e[x; y]}}
   <-->
   bind{n +@ m; x. e[nth_prefix{x; n}; nth_suffix{x; n}]}
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
