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

   Copyright (C) 2005-2006, MetaPRL Group

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
   Modified by: Aleksey Nogin @email{nogin@cs.caltech.edu}

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
extends Itt_hoas_relax

doc docoff

open Lm_printf

open Term_match_table
open Basic_tactics

open Itt_int_arith
open Itt_hoas_normalize
open Itt_hoas_debruijn
open Itt_hoas_vector
open Itt_hoas_relax
open Itt_hoas_bterm
open Itt_hoas_lof
open Itt_equal
open Itt_omega
open Itt_struct

let resource private select +=
   relax_term, OptionAllow

(************************************************************************
 * Define a table of substitutions we want to apply eagerly.
 * This should actually be placed back somewhere with the forward
 * chainer.
 *)
let extract_forward_subst_data =
   let lookup_mem table t =
      match lookup table (fun _ -> true) t with
         Some _ -> true
       | None -> false
   in
   let equal_in_table table t =
      if is_equal_term t then
         let t1, t2, t3 = dest_equal t in
            if alpha_equal t2 t3 then
               0
            else
               if lookup_mem table t then
                  1
               else
                  let t = mk_equal_term t1 t3 t2 in
                     if lookup_mem table t then
                        -1
                     else
                        0
      else
         0
   in
   let rec search table i hyps =
      match hyps with
         h :: hyps ->
            let flag =
               match h with
                  Hypothesis (_, t) ->
                     equal_in_table table t
                | Context _ ->
                     0
            in
               if flag < 0 then
                  revHypSubstT i 0 thenT search table (succ i) hyps
               else if flag > 0 then
                  hypSubstT i 0 thenT search table (succ i) hyps
               else
                  search table (succ i) hyps
       | [] ->
            idT
   in
   let forward table =
      funT (fun p ->
            let hyps = (explode_sequent (goal p)).sequent_hyps in
               search table 1 (SeqHyp.to_list hyps))
   in
      forward

let resource (term * unit, tactic) forward_subst =
   table_resource_info extract_forward_subst_data

let forward_substT = funT (fun p ->
   get_resource_arg p get_forward_subst_resource)

(************************************************************************
 * Forward chaining.
 *)
doc <:doc<
   Some useful rules for forward chaining.
>>
interactive subterms_forward_lemma 'n 'op : <:xrule<
   <H> >- 'n in nat -->
   <H> >- 'op in "Operator" -->
   <H> >- btl in list{Bind{n}} -->
   <H> >- mk_bterm{n; op; btl} in BTerm -->
   <H> >- btl in list{BTerm}
>>

interactive mk_bterm_subterms_forward 'H : <:xrule<
   "wf" : <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]> >- d in nat -->
   "wf" : <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]> >- op in Operator -->
   "wf" : <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]> >- subterms in list{Bind{d}} -->
   <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]>; subterms in list{BTerm} >- C[x] -->
   <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]> >- C[x]
>>

interactive mk_bterm_wf_forward 'H : <:xrule<
   "wf" : <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]> >- d in nat -->
   "wf" : <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]> >- op in Operator -->
   "wf" : <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]> >- subterms in list{Bind{d}} -->
   <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]>; compatible_shapes{d; shape{op}; subterms} >- C[x] -->
   <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]> >- C[x]
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
interactive mk_bterm_wf_forward2 {| forward [ForwardPrec forward_trivial_prec] |} 'H : <:xrule<
   "wf" : <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]> >- d in nat -->
   "wf" : <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]> >- op in Operator -->
   "wf" : <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]> >- subterms in list{Bind{d}} -->
   <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]>;
      subterms in list{BTerm};
      compatible_shapes{d; shape{op}; subterms}
      >- C[x] -->
   <H>; x: mk_bterm{d; op; subterms} in BTerm; <J[x]> >- C[x]
>>

interactive mk_bterm_wf_forward3 {| forward [ForwardPrec forward_trivial_prec] |} 'H : <:xrule<
   "wf" : <H>; x: mk_bterm{d; op; subterms} in BTerm{n}; <J[x]> >- d in nat -->
   "wf" : <H>; x: mk_bterm{d; op; subterms} in BTerm{n}; <J[x]> >- op in Operator -->
   "wf" : <H>; x: mk_bterm{d; op; subterms} in BTerm{n}; <J[x]> >- subterms in list{Bind{d}} -->
   <H>; x: mk_bterm{d; op; subterms} in BTerm{n}; <J[x]>;
      d = n in nat;
      subterms in list{BTerm};
      compatible_shapes{d; shape{op}; subterms}
      >- C[x] -->
   <H>; x: mk_bterm{d; op; subterms} in BTerm{n}; <J[x]> >- C[x]
>>

doc <:doc<
   Basic rules for forward chaining.
>>
interactive cons_wf_forward {| forward [] |} 'H : <:xrule<
   <H>; x: cons{h; l} in list{t}; <J[x]>; h in t; l in list{t} >- C[x] -->
   <H>; x: cons{h; l} in list{t}; <J[x]> >- C[x]
>>

interactive and_forward {| forward [] |} 'H : <:xrule<
   <H>; x: A && B; <J[x]>; A; B >- C[x] -->
   <H>; x: A && B; <J[x]> >- C[x]
>>

interactive var_bterm2_wf {| intro |} : <:xrule<
   "wf" : <H> >- l in nat -->
   "wf" : <H> >- r in nat -->
   "aux" : <H> >- n = l +@ (r +@ 1) in nat -->
   <H> >- var{l; r} in BTerm{n}
>>

interactive var_bterm2_wf2 {| intro |} : <:xrule<
   "wf" : <H> >- l1 = l2 in nat -->
   "wf" : <H> >- r1 = r2 in nat -->
   "aux" : <H> >- n = l1 +@ (r1 +@ 1) in nat -->
   <H> >- var{l1; r1} = var{l2; r2} in BTerm{n}
>>

interactive var_bterm2_wf3 {| intro |} : <:xrule<
   "wf" : <H> >- l1 = l2 in nat -->
   "wf" : <H> >- r1 = r2 in nat -->
   <H> >- var{l1; r1} = var{l2; r2} in BTerm
>>

interactive compatible_shapes_forward1 {| forward |} 'H : <:xrule<
   "wf" : <H>; x: compatible_shapes{n; shape; subterms}; <J[x]> >- n in nat -->
   "wf" : <H>; x: compatible_shapes{n; shape; subterms}; <J[x]> >- shape in list{nat} -->
   "wf" : <H>; x: compatible_shapes{n; shape; subterms}; <J[x]> >- subterms in list{BTerm} -->
   <H>; x: compatible_shapes{n; shape; subterms}; <J[x]>;
      length{shape} = length{subterms} in nat;
      all i: Index{subterms}. bdepth{nth{subterms; i}} = nth{shape; i} +@ n in nat
      >- C[x] -->
   <H>; x: compatible_shapes{n; shape; subterms}; <J[x]> >- C[x]
>>

interactive compatible_shapes1 : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- shape in list{nat} -->
   "wf" : <H> >- subterms in list{BTerm} -->
   "aux" : <H> >- length{subterms} = length{shape} in nat -->
   "wf" : <H>; i: Index{subterms} >- bdepth{nth{subterms; i}} = nth{shape; i} +@ n in nat -->
   <H> >- compatible_shapes{n; shape; subterms}
>>

(************************************************************************
 * Additional theorems for bind.
 *
 * XXX: TODO: JYH: we need to consider some general form for these lemmas,
 * but at the moment I'm not sure exactly what it is.
 *
 * Aleksey: as I wrote on mailing list, I think that the general theorem
 * should be something like:
 *
 * t in BTerm[m] -->                                                 (1)
 * k <= m -->
 * all i:[0..k-1]. bind{n; x.ts[i; x]} in BTerms{n} -->              (2)
 * bind{n; x. t @ lof{k; i. t[i; x]} in BTerms {m -@ k +@ n}
 *
 * We would need to make sure that the LOF algebra (or some modification of it)
 * can ensure that (2) will always be auto-provable.
 *
 * P.S. The "relax" version of the above would have the "eta-expansion"
 * bind{k; x. t @x} in BTerm[m]
 * in place of (1). This "relax" version is a bit stronger on the surface (as the condition is strictly weaker), but
 * either one is trivially derivable from another and I am not sure whether we'd actually need it. Hopefully not a
 * big deal either way. 
 *)
interactive bind_subst_nth_prefix_wf_aux : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- m in nat -->
   "aux" : <H> >- m <= n -->
   "wf" : <H> >- e in BTerm -->
   "aux" : <H> >- bdepth{e} >= m -->
   <H> >- bind{n; x. substl{e; nth_prefix{x; m}}} in BTerm{bdepth{e} -@ m +@ n}
>>

interactive bind_subst_nth_prefix_wf {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- m in nat -->
   "aux" : <H> >- m <= n -->
   "wf" : <H> >- e in BTerm -->
   "aux" : <H> >- bdepth{e} >= m -->
   <H> >- bind{n; x. substl{e; nth_prefix{x; m}}} in BTerm
>>

interactive bind_subst_nth_prefix_wf2 {| intro |} : <:xrule<
   "wf" : <H> >- n in nat -->
   "wf" : <H> >- m in nat -->
   "aux" : <H> >- m <= n -->
   "wf" : <H> >- e in BTerm -->
   "aux" : <H> >- bdepth{e} >= m -->
   "aux" : <H> >- d = bdepth{e} -@ m +@ n in nat -->
   <H> >- bind{n; x. substl{e; nth_prefix{x; m}}} in BTerm{d}
>>

interactive_rw reduce_bdepth_bind_subst_nth_prefix {| reduce |} : <:xrule<
   n in nat -->
   m in nat -->
   m <= n -->
   e in BTerm -->
   bdepth{e} >= m -->
   bdepth{bind{n; x. substl{e; nth_prefix{x; m}}}}
   <-->
   bdepth{e} -@ m +@ n
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

(*
 * JYH: we seem to be coming up with a lot of arithmetic goals
 * based on the lengths of CVars.  In this case, we just normalize
 * the expression.  We don't want to normalize aggressively necessarily,
 * so we normalize conditionally.
 *)
let rec is_arith_exp t =
   match explode_term t with
      << length{'l} >> ->
         true
    | << number[i:n] >> ->
         true
    | << 'i +@ 'j >>
    | << 'i -@ 'j >>
    | << 'i *@ 'j >> ->
         is_arith_exp i && is_arith_exp j
    | _ ->
         false

let is_arith_goal t =
   match explode_term t with
      << 'e1 = 'e2 in '__e3 >>
    | << 'e1 < 'e2 >>
    | << 'e1 <= 'e2 >> ->
         is_arith_exp e1 && is_arith_exp e2
    | _ ->
         false

let proveArithT = funT (fun p ->
   if is_arith_goal (concl p) then
      rw normalizeC 0 thenT autoT
   else
      idT)

(*
 * The main tactic pulls all the parts together.
 *)
let proofRule1T =
   rw (normalizeBTermSimpleC thenC reduceC) 0
   thenT autoT

let proofRule2T =
   reduceT
   thenT forward_substT
   thenT autoT

let proofRule3T =
   tryT (arithT thenT autoT)
   thenT proveArithT

let proofRuleAuxWFT =
   autoT
   thenT proofRule1T
   thenT proofRule2T
   thenT proofRule3T

let proofRuleWFT =
   (*
    * XXX: Aleksey: Do we need this repeatT?
    * Temporary disabled as it creates infinite loops when debugging things
    *)
   withAllowOptionT relax_term ((* repeatT *) proofRuleAuxWFT)
   thenT forwardChainT
   thenT autoT

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
   let p = env_arg e in
   let ty =
      match get_with_arg p with
         Some ty -> ty
       | None -> infer_type p (dest_bdepth_term (env_term e))
   in
      reduce_bind_of_bterm2 ty

let reduceDepthBTerm2C = funC reduce_depth_of_exp

let resource reduce +=
   [<< bdepth{'e} >>, wrap_reduce_crw reduceDepthBTerm2C]

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
