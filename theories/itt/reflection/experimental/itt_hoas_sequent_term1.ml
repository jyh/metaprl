doc <:doc<
   @module[Itt_hoas_sequent_term]

   Native sequent representation, based on the @hrefterm[fsequent] operator
   defined in the @hrefmodule[Itt_vec_sequent_term] theory.

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
extends Itt_vec_bind
extends Itt_vec_list1
extends Itt_vec_sequent_term
extends Itt_hoas_vbind
extends Itt_hoas_sequent
extends Itt_hoas_sequent_bterm
extends Itt_hoas_proof
extends Itt_theory
extends Itt_match

doc docoff

open Lm_printf
open Basic_tactics
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
   l1 IN "list" -->
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
   l1 IN "list" -->
   l2 IN "list" -->
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
   <H> >- "hyp_term"{| <J> >- A |} IN "list"
>>

interactive hyps_bterms_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- l in list -->
   <H> >- hyps_bterms{l} IN "list"
>>

interactive hyp_context_wf {| intro [] |} : <:xrule<
   <H> >- "hyp_context"{| <J> >- "hyplist"{| <K> |} |} IN "list"
>>

(************************************************************************
 * Well-formedness of vsequents.
 *)
doc <:doc<
   Well-formedness of sequent terms.
>>
interactive vsequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- arg IN BTerm{0} -->
   "wf" : <H> >- "vflatten"{| <J> |} IN CVar{length{"vflatten"{| |}}} -->
   "wf" : <H> >- C IN BTerm{length{"vflatten"{| <J> |}}} -->
   <H> >- vsequent{arg}{| <J> >- C<|H|> |} IN Itt_hoas_sequent!Sequent
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
 * Forward reasoning.
 *)
interactive vsequent_wf_forward {| forward [] |} 'H : <:xrule<
   <H>; vsequent{arg}{| <J> >- C |} in Sequent; <K>;
      arg in BTerm{0};
      vflatten{| <J> |} in CVar{0};
      C in BTerm{length{vflatten{| <J> |}}} >- D -->
   <H>; vsequent{arg}{| <J> >- C<|H|> |} in Sequent; <K> >- D
>>

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
 * Length theorems.
 *)
doc <:doc<
   Length theorems.  We try to produce a normal form.  The elements
   of the list don't matter, so the usual goal is to produce
   << length{vlist{| <J> |}} >>.
>>
interactive_rw reduce_length_hyplist {| reduce |} : <:xrewrite<
   length{hyplist{| <J> |}}
   <-->
   length{vlist{| <J> |}}
>>

interactive_rw reduce_length_hyps_bterms {| reduce |} : <:xrewrite<
   l in list -->
   length{hyps_bterms{l}}
   <-->
   length{l}
>>

interactive_rw reduce_length_hyp_context_nil {| reduce |} : <:xrewrite<
   length{hyp_context{| >- hyplist{| <J> |} |}}
   <-->
   length{vlist{| <J> |}}
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
 * hyps_bterms{'e}
 *)
let hyps_bterms_term = << hyps_bterms{'e} >>
let hyps_bterms_opname = opname_of_term hyps_bterms_term
let dest_hyps_bterms_term = dest_dep0_term hyps_bterms_opname

(*
 * Reduce the bsequent.
 *)
let rec reduce_hyps t =
   let a = dest_hyps_bterms_term t in
      if is_append_term a then
         reduce_hyps_bterms_append
         thenC (addrC [Subterm 1] (termC reduce_hyps))
         thenC (addrC [Subterm 2] (termC reduce_hyps))
      else
         reduce_hyps_bterms_hyplist_simple
         orelseC reduce_hyps_bterms_mk_vbind
         orelseC reduce_hyps_bterms_hyplist

let reduce_vsequent =
   addrC [Subterm 1] reduce_fsequent
   thenC reduce_vsequent_of_triple
   thenC addrC [ClauseAddr 1] (termC reduce_hyps)
   thenC addrC [ClauseAddr 0] reduce_bterm_of_mk_vbind_mk_core
   thenC repeatC (reduce_vsequent_append 1)

let reduce_bsequent =
   unfold_bsequent
   thenC addrC [Subterm 1] reduce_vsequent

(************************************************************************
 * Tests.
 *)
interactive bsequent_test_intro1 : <:xrule<
   <H> >- bsequent{it}{| <J> >- 1 +@ 2 |} IN "top"
>>

interactive bsequent_test_elim1 'J : <:xrule<
   <H> >- bsequent{it}{| <J>; x: A; <K[x]> >- 1 +@ 2 |} IN "top"
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
