doc <:doc<
   @module[Itt_hoas_sequent_term]

   Native sequent representation, based on the @hrefterm[fsequent] operator
   defined in the @hrefmodule[Itt_vec_sequent_term] theory.

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
extends Itt_vec_bind
extends Itt_vec_list1
extends Itt_vec_dform
extends Itt_vec_sequent_term
extends Itt_hoas_relax
extends Itt_hoas_vbind
extends Itt_hoas_sequent
extends Itt_hoas_sequent_bterm
extends Itt_theory
extends Itt_match

doc docoff

open Lm_printf

open Basic_tactics
open Base_trivial

open Itt_list2
open Itt_vec_sequent_term

(************************************************************************
 * Itt_vec_bind --> Itt_hoas_vbind conversion.
 *)
doc <:doc<
   Define a conversion from @tt[Itt_vec_bind] terms to BTerms.
>>
define unfold_bterm_of_vterm :
   bterm_of_vterm{'e}
   <-->
   fix{f. lambda{e. dest_bind{'e; bind{x. 'f bind_subst{'e; 'x}}; e. 'e}}} 'e

interactive_rw reduce_bterm_of_mk_bind {| reduce |} :
   bterm_of_vterm{mk_bind{x. 'e['x]}}
   <-->
   bind{x. bterm_of_vterm{'e['x]}}

interactive_rw reduce_bterm_of_mk_core {| reduce |} :
   bterm_of_vterm{mk_core{'e}}
   <-->
   'e

interactive_rw reduce_bterm_of_mk_vbind {| reduce |} :
   bterm_of_vterm{mk_vbind{| <J> >- 'C |}}
   <-->
   vbind{| <J> >- bterm_of_vterm{'C} |}

interactive_rw reduce_bterm_of_mk_vbind_mk_core {| reduce |} :
   bterm_of_vterm{mk_vbind{| <J> >- mk_core{'C} |}}
   <-->
   vbind{| <J> >- 'C |}

(************************************************************************
 * hyps_bterms.
 *)
doc <:doc<
   Convert all the hypotheses in a list to their BTerm equivalents.
>>
define unfold_hyps_bterms : hyps_bterms{'l} <--> <:xterm<
   map{t. bterm_of_vterm{t}; l}
>>

interactive_rw reduce_hyps_bterms_nil {| reduce |} : <:xrewrite<
   hyps_bterms{[]}
   <-->
   []
>>

interactive_rw reduce_hyps_bterms_cons {| reduce |} : <:xrewrite<
   hyps_bterms{u::v}
   <-->
   bterm_of_vterm{u} :: hyps_bterms{v}
>>

interactive_rw reduce_hyps_bterms_append {| reduce |} : <:xrewrite<
   l1 in list -->
   hyps_bterms{append{l1; l2}}
   <-->
   append{hyps_bterms{l1}; hyps_bterms{l2}}
>>

doc <:doc<
   The << hyp_term{| <J> >- 'A |} >> term represents a single
   BTerm hypothesis.  The << hyp_context{| <J> >- hyplist{| <K> |} |} >>
   term represents a context in the scope of @code{<J>} binders.
>>
declare sequent [hyp_term] { Term : Term >- Term } : Term

prim_rw unfold_hyp_term : hyp_term{| <J> >- 'A |} <--> <:xterm<
   ["vbind"{| <J> >- A |}]
>>

declare sequent [hyp_context] { Term : Term >- Term } : Term

prim_rw unfold_hyp_context : hyp_context{| <J> >- 'A |} <--> <:xterm<
   hyps_bterms{hyps_flatten{"mk_vbind"{| <J> >- mk_core{A} |}}}
>>

interactive_rw reduce_hyps_bterms_hyplist_simple {| reduce |} : <:xrewrite<
   hyps_bterms{"hyplist"{| <K> |}}
   <-->
   "hyp_context"{| >- "hyplist"{| <K> |} |}
>>

interactive_rw invert_hyps_bterms_hyplist_simple : <:xrewrite<
   "hyp_context"{| >- "hyplist"{| <K> |} |}
   <-->
   hyps_bterms{"hyplist"{| <K> |}}
>>

interactive_rw reduce_hyps_bterms_hyplist {| reduce |} : <:xrewrite<
   hyps_bterms{hyps_flatten{"mk_vbind"{| <J> >- mk_core{"hyplist"{| <K> |}} |}}}
   <-->
   "hyp_context"{| <J> >- "hyplist"{| <K> |} |}
>>

doc <:doc<
   Conversions from the original representation to the BTerm
   representation.
>>
interactive_rw reduce_hyps_bterms_mk_vbind {| reduce |} : <:xrewrite<
   hyps_bterms{["mk_vbind"{| <J> >- mk_core{A} |}]}
   <-->
   "hyp_term"{| <J> >- A |}
>>

interactive_rw fold_hyp_term_cons : <:xrewrite<
   vbind{| <J> >- A |} :: l
   <-->
   append{hyp_term{| <J> >- A |}; l}
>>

interactive_rw hyp_term_of_hyp_context {| reduce |} : <:xrewrite<
   hyp_context{| <J> >- hyplist{| x: A |} |}
   <-->
   hyp_term{| <J> >- A |}
>>

(************************************************************************
 * Flattened form of the sequent.
 *)
doc <:doc<
   Form the flattened vector form of the sequent from the original triple.
>>
declare sequent [vsequent{'arg}] { Term : Term >- Term } : Term

prim_rw unfold_vsequent : vsequent{'arg}{| <J> >- 'C |} <--> <:xterm<
   "sequent"{arg; "vflatten"{| <J> |}; "vsubst_dummy"{| <J> >- C |}}
>>

define unfold_vsequent_of_triple : vsequent_of_triple{'e} <--> <:xterm<
   let arg, hyps, concl = e in
      vsequent{arg}{| hyps_bterms{hyps} >- bterm_of_vterm{concl} |}
>>

interactive_rw reduce_vsequent_of_triple {| reduce |} : <:xrewrite<
   vsequent_of_triple{(a, (b, c))}
   <-->
   vsequent{a}{| hyps_bterms{b} >- bterm_of_vterm{c} |}
>>

(*
 * Flattening append.
 *)
interactive_rw reduce_vsequent_append 'J : <:xrewrite<
   l1 in list -->
   l2 in list -->
   vsequent{arg}{| <J>; append{l1<||>; l2<||>}; <K> >- C |}
   <-->
   vsequent{arg}{| <J>; l1; l2; <K> >- C |}
>>

(************************************************************************
 * Bsequent.
 *)
doc <:doc<
   The << bsequent{'arg}{| <J> >- 'C |} >> is a << Sequent >> interpretation
   of the original sequent.
>>
prim_rw unfold_bsequent : <:xrewrite<
   "bsequent"{arg}{| <J> >- C |}
   <-->
   sequent_bterm{vsequent_of_triple{"fsequent"{arg}{| <J> >- C |}}}
>>

(************************************************************************
 * Well-formedness.
 *)
doc <:doc<
   Well-formedness reasoning.
>>
interactive hyp_term_wf {| intro [] |} : <:xrule<
   <H> >- "hyp_term"{| <J> >- A |} in list
>>

interactive hyps_bterms_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l in list -->
   <H> >- hyps_bterms{l} in list
>>

interactive hyp_context_wf {| intro [] |} : <:xrule<
   <H> >- "hyp_context"{| <J> >- "hyplist"{| <K> |} |} in list
>>

interactive_rw reduce_vflatten_hyp_context_singleton {| reduce |} : <:xrule<
   vflatten{| hyp_context{| <J> >- hyplist{| <K> |} |} |}
   <-->
   hyp_context{| <J> >- hyplist{| <K> |} |}
>>

(************************************************************************
 * hyp_context{| ... |} reductions.
 *)
doc <:doc<
   Reductions for << hyp_context{| <J> >- 'C |} >>.
>>
interactive_rw reduce_hyp_context_nil {| reduce |} : <:xrewrite<
   hyp_context{| <J> >- [] |}
   <-->
   []
>>

interactive_rw reduce_hyp_context_cons : <:xrewrite<
   hyp_context{| <J> >- hyplist{| x: A; <K[x]> |} |}
   <-->
   vbind{| <J> >- A |} :: hyp_context{| <J>; x: A >- hyplist{| <K[x]> |} |}
>>

interactive_rw reduce_hyp_context_split 'K : <:xrewrite<
   hyp_context{| >- hyplist{| <K>; <L> |} |}
   <-->
   append{hyp_context{| >- hyplist{| <K> |} |}; hyp_context{| <K> >- hyplist{| <L> |} |}}
>>

(************************************************
 * Relaxed theorems.
 *)
doc <:doc<
   Relaxed theorems.
>>
interactive hyp_context_relax {| intro |} : <:xrule<
   <H> >- "hyp_context"{| <J> >- "hyplist"{| <K> |} |} in CVarRelax{bdepth{vbind{| <J> >- mk_terms{hyplist{| <K> |}} |}}}
>>

interactive hyp_context_relax_base {| intro |} : <:xrule<
   <H> >- "hyp_context"{| >- "hyplist"{| <K> |} |} in CVarRelax{0}
>>

(************************************************
 * Context squashing.
 *)
interactive_rw squash_hyp_context Perv!bind{x. hyp_context{| <J['x]> >- 'e |}} : <:xrewrite<
   hyp_context{| <J[x]> >- 'e |}
   <-->
   hyp_context{| <J[it]> >- 'e |}
>>

(************************************************************************
 * Length theorems.
 *)
doc <:doc<
   Length theorems.  We try to produce a normal form.  The elements
   of the list don't matter, so the usual goal is to produce
   << length{vlist{| <J> |}} >>.
>>
interactive_rw reduce_hyps_bterms_length {| reduce |} : <:xrewrite<
   l in list -->
   length{hyps_bterms{l}}
   <-->
   length{l}
>>

interactive_rw reduce_hyp_context_length_left {| reduce |} : <:xrewrite<
   length{hyp_context{| x: A; <J[x]> >- hyplist{| <K[x]> |} |}}
   <-->
   length{hyp_context{| <J[it]> >- hyplist{| <K[it]> |} |}}
>>

interactive_rw reduce_length_hyplist {| reduce |} : <:xrewrite<
   length{hyplist{| <J> |}}
   <-->
   length{vlist{| <J> |}}
>>

interactive_rw reduce_length_hyp_context_nil {| reduce |} : <:xrewrite<
   length{hyp_context{| >- hyplist{| <J> |} |}}
   <-->
   length{vlist{| <J> |}}
>>

interactive_rw reduce_length_hyp_term {| reduce |} : <:xrewrite<
   length{hyp_term{| <J> >- e |}}
   <-->
   1
>>

(************************************************************************
 * Well-formedness of vsequents.
 *)
doc <:doc<
   Well-formedness of sequent terms.
>>
interactive vsequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- arg in BTerm{0} -->
   "wf" : <H> >- vflatten{| <J> |} in CVar{length{vflatten{| |}}} -->
   "wf" : <H> >- C in BTerm{length{vflatten{| <J> |}}} -->
   <H> >- vsequent{arg}{| <J> >- C<|H|> |} in Sequent
>>

interactive vsequent_equal {| intro [] |} : <:xrule<
   "wf" : <H> >- arg1 = arg2 in BTerm{0} -->
   "wf" : <H> >- vflatten{| <J1> |} = vflatten{| <J2> |} in CVar{length{vflatten{||}}} -->
   "wf" : <H> >- C1 = C2 in BTerm{length{vflatten{| <J1> |}}} -->
   <H> >- vsequent{arg1}{| <J1> >- C1<|H|> |} = vsequent{arg2}{| <J2> >- C2<|H|> |} in Sequent
>>

interactive vflatten_hyp_concl_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- d IN "nat" -->
   <H> >- "vflatten"{| |} IN CVar{d}
>>

interactive vflatten_hyp_left_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- "vlist"{| <K> |} IN list{"list"} -->
   "wf" : <H> >- A IN CVar{length{"vflatten"{| <K> |}}} -->
   "wf" : <H> >- "vflatten"{| <J[it]> |} IN CVar{length{"vflatten"{| <K>; x: A |}}} -->
   <H> >- "vflatten"{| x: A; <J[x]> |} IN CVar{length{"vflatten"{| <K> |}}}
>>

interactive hyp_term_cvar_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- vbind{| <J> >- e |} in BTerm{n} -->
   <H> >- hyp_term{| <J> >- e |} in CVar{n}
>>

(************************************************************************
 * Normalization.
 *)
doc <:doc<
   Define the rewrites that turn a @tt[bsequent] into a normalized @tt[vsequent].
>>
interactive_rw reduce_bsequent_start : <:xrewrite<
   bsequent{arg}{| <J> >- C |}
   <-->
   sequent_bterm{vsequent{arg}{| hyp_context{| >- hyplist{| <J> |} |} >- vbind{| <J> >- C |} |}}
>>

interactive_rw reduce_vsequent_nil {| reduce |} : <:xrewrite<
   vsequent{arg}{| hyp_context{| >- hyplist{||} |}; <J> >- C |}
   <-->
   vsequent{arg}{| <J> >- C |}
>>

interactive_rw reduce_vsequent_split 'J : <:xrewrite<
   vsequent{arg}{| hyp_context{| >- hyplist{| <J>; <K> |} |}; <L> >- C |}
   <-->
   vsequent{arg}{| hyp_context{| >- hyplist{| <J> |} |};
                   hyp_context{| <J> >- hyplist{| <K> |} |};
                   <L>
                   >- C
                |}
>>

interactive_rw reduce_vsequent_right : <:xrewrite<
   vsequent{arg}{| hyp_context{| >- hyplist{| <J>; A |} |}; <L> >- C |}
   <-->
   vsequent{arg}{| hyp_context{| >- hyplist{| <J> |} |};
                   hyp_term{| <J> >- A |};
                   <L>
                   >- C
                |}
>>

(*
interactive_rw reduce_bsequent 'J : <:xrewrite<
   bsequent{arg}{| <J>; x: A; <K[x]> >- C[x] |}
   <-->
   sequent_bterm{vsequent{arg}{| hyp_context{| >- hyplist{| <J> |} |};
                                 hyp_term{| <J> >- A |};
                                 hyp_context{| <J>; x: A >- hyplist{| <K[x]> |} |}
                                 >- vbind{| <J>; x: A; <K[x]> >- C[x] |}
                              |}}
>>
 *)

(************************************************************************
 * Forward reasoning.
 *)
doc <:doc<
   Forward reasoning.  The @tt[vsequent_wf_forward] rule has some auxiliary
   relaxed subgoals.  For the @tt[bsequent] form, these goals are automatically
   true, so we do the actual forward chaining on the @tt[bsequent] form.
>>
interactive vsequent_wf_forward {| forward |} 'H : <:xrule<
   <H>; vsequent{arg1}{| <J1> >- C1<|H|> |} = vsequent{arg2}{| <J2> >- C2<|H|> |} in Sequent; <K>;
      arg1 = arg2 in BTerm{0};
      vflatten{| <J1> |} = vflatten{| <J2> |} in CVar{length{vflatten{||}}};
      C1 = C2 in BTerm{length{vflatten{| <J1> |}}} >- D -->
   <H>; vsequent{arg1}{| <J1> >- C1<|H|> |} = vsequent{arg2}{| <J2> >- C2<|H|> |} in Sequent; <K> >- D
>>

(*
 * For the following two bsequent forward-chaining theorems,
 * translate into a vsequent, then use a tactic to reduce
 * the vsequent hyps.
 *)
interactive bsequent_wf_forward 'H : <:xrule<
   <H>; bsequent{arg}{| <J> >- C |} in BSequent; <K>;
      arg in BTerm{0};
      hyp_context{| >- hyplist{| <J> |} |} in CVar{0};
      vbind{| <J> >- C |} in BTerm{length{vlist{| <J> |}}}
      >- D -->
   <H>; bsequent{arg}{| <J> >- C |} in BSequent; <K> >- D
>>

interactive bsequent_wf_forward2 'H : <:xrule<
   <H>; bsequent{arg}{| <J> >- C |} in BSequent; <K>;
      vsequent{arg}{| hyp_context{| >- hyplist{| <J> |} |} >- vbind{| <J> >- C |} |} in Sequent
      >- D -->
   <H>; bsequent{arg}{| <J> >- C |} in BSequent; <K> >- D
>>

(*
 * Hyps forward-chaining.
 *)
interactive vflatten_wf_forward_left {| forward [] |} 'H : <:xrule<
   "wf" : <H>; vflatten{| A; <J> |} in CVar{n}; <K> >- n in nat -->
   "wf" : <H>; vflatten{| A; <J> |} in CVar{n}; <K> >- A in list{BTerm} -->
   "wf" : <H>; vflatten{| A; <J> |} in CVar{n}; <K> >- vflatten{| <J> |} in list{BTerm} -->
   <H>; vflatten{| A; <J> |} in CVar{n}; <K>; A in CVar{n}; vflatten{| <J> |} in CVar{n +@ length{A}} >- C -->
   <H>; vflatten{| A; <J> |} in CVar{n}; <K> >- C
>>

interactive_rw reduce_vflatten_hyp_term {| reduce |} : <:xrewrite<
   vflatten{| hyp_term{| <J> >- e |} |}
   <-->
   [vbind{| <J> >- e |}]
>>

(************************************************************************
 * Tactics.
 *)
let fold_bterm_of_vterm = makeFoldC << bterm_of_vterm{'e} >> unfold_bterm_of_vterm
let fold_hyp_term = makeFoldC << hyp_term{| <J> >- 'A |} >> unfold_hyp_term
let fold_hyp_context = makeFoldC << hyp_context{| <J> >- 'A |} >> unfold_hyp_context

(*
 * hyp_context{| <J> >- 'A |}
 *)
let hyp_context_arg_term = << hyp_context >>
let hyp_context_arg_opname = opname_of_term hyp_context_arg_term
let is_hyp_context_arg_term = is_no_subterms_term hyp_context_arg_opname

let is_hyp_context_term t =
   is_sequent_term t && is_hyp_context_arg_term (sequent_args t)

let dest_hyp_context_term t =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in
      if is_hyp_context_arg_term arg then
         hyps, concl
      else
         raise (RefineError ("dest_hyp_context_term", StringTermError ("not a hyp_context term", t)))

(*
 * vsequent{| <J> >- 'A |}
 *)
let vsequent_arg_term = << vsequent{'arg} >>
let vsequent_arg_opname = opname_of_term vsequent_arg_term
let is_vsequent_arg_term = is_dep0_term vsequent_arg_opname
let dest_vsequent_arg_term = dest_dep0_term vsequent_arg_opname

let is_vsequent_term t =
   is_sequent_term t && is_vsequent_arg_term (sequent_args t)

let dest_vsequent_term t =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in
   let arg = dest_vsequent_arg_term arg in
      arg, hyps, concl

(*
 * vsequent reduction.
 *)
let reduce_vsequent_conv t =
   let _, hyps, _ = dest_vsequent_term t in
      if SeqHyp.length hyps = 0 then
         raise (RefineError ("reduce_vsequent_conv", StringTermError ("empty hypotheses", t)));
      match SeqHyp.get hyps 0 with
         Context _ ->
            raise (RefineError ("reduce_vsequent_conv", StringTermError ("illegal context", t)))
       | Hypothesis (_, t) ->
            let hyps, concl = dest_hyp_context_term t in
            let hyps = dest_hyplist_term concl in
            let len = SeqHyp.length hyps in
               if len = 0 then
                  reduce_vsequent_nil
               else if len = 1 then
                  match SeqHyp.get hyps 0 with
                     Hypothesis _ ->
                        reduce_vsequent_right thenC reduce_vsequent_nil
                   | Context _ ->
                        raise (RefineError ("reduce_vsequent_conv", StringTermError ("already reduced", t)))
               else
                  let finish =
                     match SeqHyp.get hyps 0 with
                        Hypothesis _ ->
                           reduce_vsequent_right thenC reduce_vsequent_nil
                      | Context _ ->
                           idC
                  in
                  let rec collect i =
                     if i = 0 then
                        finish
                     else
                        match SeqHyp.get hyps i with
                           Hypothesis _ ->
                              reduce_vsequent_right thenC collect (pred i)
                         | Context _ ->
                              reduce_vsequent_split (succ i) thenC collect (pred i)
                  in
                     collect (pred len)

let reduce_vsequent = termC reduce_vsequent_conv

let reduce_bsequent =
   reduce_bsequent_start
   thenC addrC [Subterm 1] (tryC reduce_vsequent)

let resource reduce +=
    [<:xterm< vsequent{arg}{| hyp_context{| <J> >- C |}; <K> >- D |} >>, wrap_reduce reduce_vsequent]

(*
 * Perform reduction during forward-chaining.
 *)
let forward_bsequent_wf i =
    bsequent_wf_forward2 i
    thenT rw (addrC [Subterm 2] (tryC reduce_vsequent)) (-1)
    thenT rw (addrC [Subterm 3] (tryC reduce_vsequent)) (-2)

(*
 * JYH: we don't need this for now because the Itt_hoas_sequent_proof.provable_forwardT
 * calls it manually.
let resource forward +=
    [<:xterm< bsequent{arg}{| <J> >- C |} in BSequent >>,
        { forward_loc  = (LOCATION);
          forward_prec = forward_trivial_prec;
          forward_tac  = forward_bsequent_wf
        }]
 *)

(************************************************
 * Squash as much as possible in the << hyp_context{| <J> >- 'e |} >> hyp list.
 *)
let var_x = Lm_symbol.add "x"

let squash_hyp_context_conv t =
   let { sequent_args = arg;
         sequent_hyps = hyps;
         sequent_concl = concl
       } = explode_sequent t
   in

   (*
    * Find the term to be replaced.
    *)
   let hyps = (explode_sequent t).sequent_hyps in
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
      squash_hyp_context t_bind

let resource reduce +=
    [<< hyp_context{| <J> >- 'e |} >>, wrap_reduce (termC squash_hyp_context_conv)]

(************************************************************************
 * Tests.
 *)
interactive bsequent_test_intro1 : <:xrule<
   <H> >- bsequent{it}{| <J> >- 1 +@ 2 |} IN "top"
>>

interactive bsequent_test_elim1 'J : <:xrule<
   <H> >- bsequent{it}{| <J>; x: A; <K[x]> >- 1 +@ 2 |} IN "top"
>>

(************************************************************************
 * Display.
 *)
dform vsequent_df : vsequent{'arg}{| <H> >- 'C |} =
   szone pushm[0] pushm[3] `"vsequent[" slot{'arg} `"] {" hspace
   hspace display_sequent{vsequent{it}{| <H> >- 'C |}}
   popm hspace `"}" popm ezone

dform vsequent_hyp_df : display_hyp{vsequent{'arg}; v. 'e} =
   slot{'e}

dform vsequent_concl_df : display_concl{vsequent{'arg}; 'C} =
   hspace szone pushm[3] Mpsymbols!vdash `" " slot{'C} popm ezone

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
