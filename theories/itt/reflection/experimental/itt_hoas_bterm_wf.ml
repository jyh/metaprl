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
extends Itt_omega
extends Itt_int_arith
extends Itt_vec_list1
extends Itt_vec_sequent_term
extends Itt_hoas_bterm
extends Itt_hoas_lof
extends Itt_hoas_lof_vec
extends Itt_hoas_normalize

doc docoff

open Lm_printf
open Basic_tactics
open Itt_int_arith
open Itt_hoas_normalize
open Itt_hoas_debruijn
open Itt_hoas_vector
open Itt_hoas_bterm
open Itt_hoas_lof
open Itt_equal
open Itt_omega
open Itt_struct

(************************************************************************
 * Forward chaining.
 *)
doc <:doc<
   Some useful rules for forward chaining.
>>
interactive  subterms_forward_lemma 'n 'op : <:xrule<
   <H> >- 'n in nat -->
   <H> >- 'op in "Operator" -->
   <H> >- mk_bterm{'n; 'op; 'btl} in BTerm -->
   <H> >- 'btl in list{BTerm}
>>

interactive bterm2_forward {| forward [] |} 'H : <:xrule<
   <H>; e in BTerm{d}; <J>; e in BTerm; bdepth{e} = d in nat >- C -->
   <H>; e in BTerm{d}; <J> >- C
>>

interactive mk_bterm_depth_forward 'H : <:xrule<
   <H>; mk_bterm{d; op; subterms} in BTerm; <J>; d in nat >- C -->
   <H>; mk_bterm{d; op; subterms} in BTerm; <J> >- C
>>

interactive mk_bterm_op_forward 'H : <:xrule<
   <H>; mk_bterm{d; op; subterms} in BTerm; <J>; op in "Operator" >- C -->
   <H>; mk_bterm{d; op; subterms} in BTerm; <J> >- C
>>

interactive mk_bterm_subterms_forward1 'H : <:xrule<
   <H>; mk_bterm{d; op; subterms} in BTerm; <J>; subterms in list{BTerm} >- C -->
   <H>; mk_bterm{d; op; subterms} in BTerm; <J> >- C
>>

interactive mk_bterm_wf_forward 'H : <:xrule<
   <H>; mk_bterm{d; op; subterms} in BTerm; <J>; compatible_shapes{d; shape{op}; subterms} >- C -->
   <H>; mk_bterm{d; op; subterms} in BTerm; <J> >- C
>>

doc <:doc<
   For <:xterm< compatible_shapes{d; shape{op}; subterms} >>, reduce the shape,
   then chain through the subterms.
>>
let dupReduceT i =
   dupHypT i thenT rw reduceC (-1)

let resource forward +=
   [<< 't >>, { forward_loc = (LOCATION); forward_prec = forward_normal_prec; forward_tac = dupReduceT }]

doc <:doc<
   Combine them all into a single forward-chaining theorem,
   just for efficiency.
>>
interactive mk_bterm_wf_forward2 {| forward [] |} 'H : <:xrule<
   <H>; mk_bterm{d; op; subterms} in BTerm; <J>;
      d in nat;
      op in "Operator";
      subterms in list{BTerm};
      compatible_shapes{d; shape{op}; subterms}
      >- C -->
   <H>; mk_bterm{d; op; subterms} in BTerm; <J> >- C
>>

doc <:doc<
   Basic rules for forward chaining.
>>
interactive cons_wf_forward {| forward [] |} 'H : <:xrule<
   <H>; cons{h; l} in list{t}; <J>; h in t; l in list{t} >- C -->
   <H>; cons{h; l} in list{t}; <J> >- C
>>

interactive and_forward {| forward [] |} 'H : <:xrule<
   <H>; A && B; <J>; A; B >- C -->
   <H>; A && B; <J> >- C
>>

(************************************************************************
 * Tactics.
 *)
doc <:doc<
   The @tt[bindWFT] tactic is used to prove well-formedness of
   concrete non-normalized terms.  The tactic normalizes the
   term, then applies the appropriate well-formedness rule.
>>
let bind_wf p =
   let t = concl p in
   let _, t1, t2 = dest_equal t in
      if is_lof_bind_term t1 && is_lof_bind_term t2 then
         rw (higherC normalizeBTermC) 0
         thenT (mk_bterm_wf orelseT mk_bterm_wf2)
      else
         raise (RefineError ("bind_wf", StringTermError ("not a bind wf term", t)))

let bindWFT = funT bind_wf

let bind_wf = wrap_intro bindWFT

let resource intro +=
   [<< lof_bind{'n; x. 'e['x]} in BTerm >>, bind_wf;
    << lof_bind{'n; x. 'e['x]} in BTerm{'m} >>, bind_wf]

let proofRuleAuxWFT =
   autoT
   thenT rw normalizeBTermSimpleC 0
   thenT autoT
   thenT rw reduceC 0
   thenT tryT arithT
   thenT tcaT

let proofRuleWFT =
   repeatT proofRuleAuxWFT

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
