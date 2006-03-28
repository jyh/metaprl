doc <:doc<
   @module[Itt_hoas_vbind]
   The @tt[Itt_hoas_vbind] module defines a ``vector binding''
   using context notation.  We define a conversion to Itt_vec_bind.mk_vbind.

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

extends Itt_vec_bind
extends Itt_hoas_base
extends Meta_context_theory

doc docoff

open Lm_printf
open Basic_tactics
open Base_trivial
open Itt_squiggle
open Itt_struct

doc <:doc<
   @terms

   The << vbind{| <J> >- 'C |} >> is a ``vector binding'' with binders
   @code{<J>} and body << 'C >>.  The actual values of the hypotheses
   do not matter.
>>
declare sequent [vbind] { Term : Term >- Term } : Term

prim_rw unfold_vbind : vbind{| <J> >- 'C |} <-->
   sequent_ind{u, v. bind{x. happly{'v; 'x}}; TermSequent{| <J> >- 'C |}}

interactive_rw reduce_vbind_nil {| reduce |} :
   vbind{| >- 'C |}
   <-->
   'C

interactive_rw reduce_vbind_left :
   vbind{| x: 'A; <J['x]> >- 'C['x] |}
   <-->
   bind{x. vbind{| <J['x]> >- 'C['x] |}}

interactive_rw reduce_vbind_right :
   vbind{| <J>; x: 'A >- 'C['x] |}
   <-->
   vbind{| <J> >- bind{x. 'C['x]} |}

interactive_rw reduce_vbind_merge :
   vbind{| <J> >- vbind{| <K> >- 'e |} |}
   <-->
   vbind{| <J>; <K> >- 'e |}

interactive_rw reduce_vbind_split 'J :
   vbind{| <J>; <K> >- 'e |}
   <-->
   vbind{| <J> >- vbind{| <K> >- 'e |} |}

(************************************************************************
 * Hyp squashing.
 *)
interactive_rw squash_lambda_vbind : <:xrewrite<
   lambda{x. vbind{| <J[x]> >- e |}}
   <-->
   lambda{x. vbind{| <J[it]> >- e |}}
>>

interactive_rw squash_vbind Perv!bind{x. vbind{| <J['x]> >- 'e |}} : <:xrewrite<
   vbind{| <J[x]> >- 'e |}
   <-->
   vbind{| <J[it]> >- 'e |}
>>

(************************************************************************
 * Tactics.
 *)
let var_x = Lm_symbol.add "x"

(*
 * vbind{| <J> >- 'A |}
 *)
let vbind_arg_term = << vbind >>
let vbind_arg_opname = opname_of_term vbind_arg_term
let is_vbind_arg_term = is_no_subterms_term vbind_arg_opname

let is_vbind_term t =
   is_sequent_term t && is_vbind_arg_term (sequent_args t)

let dest_vbind_term t =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in
      if is_vbind_arg_term arg then
         hyps, concl
      else
         raise (RefineError ("dest_vbind_term", StringTermError ("not a vbind term", t)))

(*
 * VBind wrapping (for induction).
 *)
let mk_empty_vbind_term t =
   <:con< sequent [vbind] { >- $t$ } >>

let wrap_vbind p =
   let t = concl p in
   let t1, t2 = dest_squiggle t in
   let t1 = mk_empty_vbind_term t1 in
   let t2 = mk_empty_vbind_term t2 in
   let t = mk_squiggle_term t1 t2 in
      assertT t
      thenLT [idT; rw (addrC [Subterm 1] reduceTopC thenC addrC [Subterm 2] reduceTopC) (-1) thenT nthHypT (-1)]

let wrapVBindT = funT wrap_vbind

(*
 * Squash as much as possible in the << vbind{| <J> >- 'e |} >> hyp list.
 *)
let squash_vbind_conv t =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in

   (*
    * Find the term to be replaced.
    *)
   let x = maybe_new_var_set var_x (all_vars t) in
   let x_t = mk_var_term x in
   let rec search rev_hyps hyps =
      match hyps with
         [] ->
            raise (RefineError ("reduce_length_fun_term_conv", StringTermError ("already converted", t)))
       | Context (z, cv, args) as hyp :: hyps ->
            let rec search_args rev_args args =
               match args with
                  arg :: args ->
                     if is_it_term arg then
                        search_args (arg :: rev_args) args
                     else
                        rev_hyps, Context (z, cv, List.rev_append rev_args (x_t :: args)), hyps
                | [] ->
                     search (hyp :: rev_hyps) hyps
            in
               search_args [] args
       | Hypothesis (z, t) as hyp :: hyps ->
            if is_it_term t then
               search (hyp :: rev_hyps) hyps
            else
               rev_hyps, Hypothesis (z, x_t), hyps
   in
   let rev_hyps, hyp, hyps = search [] (SeqHyp.to_list hyps) in
   let eseq =
      { sequent_args = arg;
        sequent_hyps = SeqHyp.of_list (List.rev_append rev_hyps (hyp :: hyps));
        sequent_concl = concl
      }
   in
   let t_var = mk_sequent_term eseq in
   let t_bind = mk_bind1_term x t_var in
      squash_vbind t_bind

let squash_vbindC = termC squash_vbind_conv

let resource reduce +=
    [<< vbind{| <J> >- 'e |} >>, wrap_reduce squash_vbindC]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
