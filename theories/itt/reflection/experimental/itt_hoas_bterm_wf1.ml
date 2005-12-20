doc <:doc<
   @module[Itt_hoas_bterm_wf]
   The @tt[Itt_hoas_bterm_wf] module defines additional well-formedness
   rules for BTerms.

   This file defines a normalization procedure for concrete << BTerm >>
   that does the following.

   @begin[enumerate]
   @item{{All subterm lists are represented with a << list_of_fun{i. 'f['i]; 'n} >>
      term}}
   @end[enumerate]

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
extends Itt_list3

doc docoff

open Lm_printf
open Basic_tactics
open Itt_hoas_base
open Itt_hoas_vector
open Itt_hoas_debruijn
open Itt_equal
open Itt_list

(************************************************************************
 * We need some constants that are always natural numbers.
 * Temporarily put this here until we figure out how
 * to do it exactly.
 *)
define unfold_natural_number : natural_number[i:n] <-->
   max{number[i:n]; 0}

interactive natural_number_wf {| intro [] |} :
   sequent { <H> >- natural_number[i:n] in nat }

(*
 * This is a conversion for coding the addition.
 *    natural_number[i:n] +@ 1 --> natural_number[i+1:n]
 *
 * XXX: probably should not use reduceC.
 *)
let fold_natural_number = makeFoldC << natural_number[i:n] >> unfold_natural_number

let fold_natural_number_conv t =
   foldC <:con< max{$t$; number[0]} >> reduceC
   thenC fold_natural_number

let reduce_natural_number_succC =
   addrC [Subterm 1] unfold_natural_number
   thenC reduceC
   thenC (termC fold_natural_number_conv)

(************************************************************************
 * In-place list_of_fun adding.
 *)
doc <:doc<
   The first step is to replace concrete subterm lists << 'l >> with a
   << list_of_fun{i. nth_elem{'l; 'i}; 'n} >> term.  This is done in steps
   from the tail of the list.
>>

interactive_rw fold_list_of_fun_nil_gen :
   nil
   <-->
   list_of_fun{i. it; natural_number[0]}

interactive_rw fold_list_of_fun_cons_gen : <:xrewrite<
   n IN "nat" -->
   cons{e; list_of_fun{i. f[i]; n}}
   <-->
   list_of_fun{i. if beq_int{i; 0} then e else f[i -@ 1]; n +@ 1}
>>

interactive_rw fold_list_of_fun_cons_const : <:xrewrite<
   cons{e; list_of_fun{i. f[i]; "natural_number"[n:n]}}
   <-->
   list_of_fun{i. if beq_int{i; 0} then e else f[i -@ 1]; "natural_number"[n:n] +@ 1}
>>

(************************************************************************
 * Tactics.
 *)

(*
 * First, define a conversion that converts a concrete list into a
 * list_of_fun.
 *)
let rec find_nil_rev_address addr t =
   if is_cons_term t then
      let _, t = dest_cons t in
      let addr = Subterm 2 :: addr in
         find_nil_rev_address addr t
   else if is_nil_term t then
      addr
   else
      raise (RefineError ("find_nil_rev_address", StringTermError ("not a list term", t)))

let list_of_fun_of_concrete_list t =
   let raddr = find_nil_rev_address [] t in
   let rec foldC raddr =
      match raddr with
         [] ->
            idC
       | _ :: rest ->
            addrC (List.rev rest) fold_list_of_fun_cons_const
            thenC addrC (List.rev (Subterm 2 :: rest)) reduce_natural_number_succC
            thenC foldC rest
   in
      addrC raddr fold_list_of_fun_nil_gen
      thenC foldC raddr
      thenC addrC [Subterm 2] (unfold_natural_number thenC reduceC)

let fold_list_of_funC = termC list_of_fun_of_concrete_list

(*
 * Next, given a concrete term, make sure it is a mk_bterm,
 * and fold the subterms into a list_of_fun.
 *)
let normalize_term_subterms t =
   let preC =
      if is_mk_term_term t then
         fold_mk_term
      else if is_mk_bterm_term t then
         idC
      else
         raise (RefineError ("normalize_term_subterms", StringTermError ("not a mk_[b]term", t)))
   in
      preC thenC addrC [Subterm 3] fold_list_of_funC

let normalize_term_subtermsC = termC normalize_term_subterms

(*
 * To push a bindn into a term,
 * invoke the appropriate tactic.
 *)
let push_bind t =
   if is_bindn_term t then
      addrC [Subterm 2] normalize_term_subtermsC
      thenC reduce_vec_bind_of_mk_bterm_of_list_of_fun
   else
      raise (RefineError ("push_bind", StringTermError ("not a bindn term", t)))

let push_bindC = termC push_bind

doc <:doc<
   The @tt[normalizeBTermC] conversion normalizes a concrete BTerm,
   by performing the steps as described at the beginning of this
   module.

   @docoff
>>


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

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
