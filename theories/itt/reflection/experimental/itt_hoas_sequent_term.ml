doc <:doc<
   Native sequent representation, based on Itt_vec_sequent_term.fsequent.

   ----------------------------------------------------------------

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
extends Itt_vec_sequent_term
extends Itt_hoas_vbind
extends Itt_hoas_sequent
extends Itt_theory
extends Itt_match

doc docoff

open Basic_tactics

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

(************************************************************************
 * hyps_bterms.
 *)
doc <:doc<
   Convert all the hypotheses in a list to their BTerm equivalents.
>>
define unfold_hyps_bterms : hyps_bterms{'l} <--> <:xterm<
   map{t. bterm_of_vterm{t}; l}
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

doc <:doc<
   Conversions from the original representation to the BTerm
   representation.
>>
interactive_rw reduce_hyps_bterms_append {| reduce |} : <:xrewrite<
   l1 IN "list" -->
   hyps_bterms{append{l1; l2}}
   <-->
   append{hyps_bterms{l1}; hyps_bterms{l2}}
>>

interactive_rw reduce_hyps_bterms_mk_vbind {| reduce |} : <:xrewrite<
   hyps_bterms{["mk_vbind"{| <J> >- A |}]}
   <-->
   "hyp_term"{| <J> >- A |}
>>

interactive_rw reduce_hyps_bterms_hyplist {| reduce |} : <:xrewrite<
   hyps_bterms{hyps_flatten{"mk_vbind"{| <J> >- mk_core{"hyplist"{| <K> |}} |}}}
   <-->
   "hyp_context"{| <J> >- "hyplist"{| <K> |} |}
>>

doc <:doc<
   Form the sequent from the original triple.
>>
define unfold_sequent_of_triple : sequent_of_triple{'e} <--> <:xterm<
   let arg, hyps, concl = e in
      "sequent"{arg; hyps_bterms{hyps}; bterm_of_vterm{concl}}
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
   sequent_of_triple{"fsequent"{arg}{| <J> >- C |}}
>>

(************************************************************************
 * Well-formedness.
 *)
declare sequent [sequent_wf] { Term : Term >- Term } : Term

(************************************************************************
 * The wf theorem.
 *)
interactive bsequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- arg IN BTerm{0} -->
   "wf" : <H> >- "sequent_wf"{| <J> >- C |} -->
   <H> >- bsequent{arg}{| <J> >- C |} IN "Sequent"
>>

(************************************************************************
 * Tactics.
 *)
let fold_bterm_of_vterm = makeFoldC << bterm_of_vterm{'e} >> unfold_bterm_of_vterm

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
