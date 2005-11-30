doc <:doc<
   Native sequent representation.  This representation of sequents
   is not a BTerm itself.  If you want to work in a theory where
   sequents are not part of your language, then you should probably
   use this representation, because it is easier to use.

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
extends Itt_hoas_sequent_term
extends Itt_hoas_vec_bind
extends Itt_match

doc docoff

open Basic_tactics

(************************************************************************
 * Hypothesis list.
 *)
doc <:doc<
   The << hyplist{| <J> |} >> term produces a list of BTerms defined
   by the context J, with increasing depths.
>>
declare sequent [hyplist] { Term : Term >- Term } : Term

prim_rw unfold_hyplist : <:xrewrite<
   "hyplist"{| <J> >- C |}
   <-->
   fst{"pre_sequent"{| <J> >- "dummy_bterm" |}}
>>

doc <:doc<
   Define well-formed hyp lists.
>>
declare sequent [hyplist_wf] { Term : Term >- Term } : Term

prim_rw unfold_hyplist_wf : <:xrewrite<
   "hyplist_wf"{| <J> >- C |}
   <-->
   "sequent_wf"{| <J> >- "dummy_bterm" |}
>>

doc <:doc<
   A << hyplist{| <J> >- 'C |} >> defines a list of BTerms.
>>
interactive hyplist_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- "hyplist_wf"{| <J> |} -->
   <H> >- "hyplist"{| <J> >- C |} IN CVar{0}
>>

doc docoff

(************************************************************************
 * Define a sequent conversion that works at a depth.
 *)
declare sequent [std_sequent{'d}] { Term : Term >- Term } : Term

prim_rw unfold_std_sequent_depth : <:xrewrite<
   std_sequent{d}{| <J> >- C |}
   <-->
   sequent_ind{u, v. $'[d] shyp{u; x. $,happly{v; x}}; "TermSequent"{| <J> >- $'[d] sconcl{C} |}}
>>

interactive_rw std_sequent_depth_concl {| reduce |} : <:xrewrite<
   std_sequent{d}{| >- C |}
   <-->
   $'[d] sconcl{C}
>>

interactive_rw std_sequent_depth_left {| reduce |} : <:xrewrite<
   std_sequent{d}{| x: A; <J[x]> >- C[x] |}
   <-->
   $'[d] shyp{A; x. $,std_sequent{d}{| <J[x]> >- C[x] |}}
>>

(************************************************************************
 * Conclusion.
 *
 * Compute the conclusion directly, rather that going through flatten_sequent,
 * because the projections are a pain.
 *)

define unfold_concl_sequent : concl_sequent{'e} <--> <:xterm<
   (fix f e ->
       dest_bterm e with
          l, r -> "Invalid_argument"
        | d, o, s ->
             if is_same_op{o; $shyp{h; x. rest}} then
                f nth{s; 1}
             else if is_same_op{o; $sconcl{e}} then
                nth{s; 0}
             else
                "Invalid_argument") e
>>

let fold_concl_sequent = makeFoldC << concl_sequent{'e} >> unfold_concl_sequent

interactive_rw reduce_concl_sequent : <:xrewrite<
   concl_sequent{e}
   <-->
   dest_bterm e with
      l, r -> "Invalid_argument"
    | d, o, s ->
         if is_same_op{o; $shyp{h; x. rest}} then
            concl_sequent{nth{s; 1}}
         else if is_same_op{o; $sconcl{e}} then
            nth{s; 0}
         else
            "Invalid_argument"
>>

interactive_rw reduce_concl_sequent_concl {| reduce |} : <:xrewrite<
   d IN "nat" -->
   e IN BTerm{d} -->
   concl_sequent{$'[d] sconcl{e}}
   <-->
   e
>>

interactive_rw reduce_concl_sequent_hyp {| reduce |} : <:xrewrite<
   d IN "nat" -->
   e1 IN BTerm{d} -->
   e2 IN BTerm{d +@ 1} -->
   concl_sequent{mk_bterm{d; $shyp{e; x. r}; [e1; e2]}}
   <-->
   concl_sequent{e2}
>>

(*
 * Sequent form.
 *)
declare sequent [con_sequent{'d}] { Term : Term >- Term } : Term

prim_rw unfold_con_sequent : <:xrewrite<
   con_sequent{d}{| <J> >- C |}
   <-->
   concl_sequent{std_sequent{d}{| <J> >- C |}}
>>

interactive_rw reduce_con_sequent_concl {| reduce |} : <:xrewrite<
   d IN "nat" -->
   C IN BTerm{d} -->
   con_sequent{d}{| >- C |}
   <-->
   C
>>

define unfold_con_sequent_concl : con_sequent_concl{'e} <-->
   con_sequent{bdepth{'e}}{| >- 'e |}

interactive_rw reduce_con_sequent_concl_lemma : <:xrewrite<
   "vbind"{| <J> >- "vbind"{| >- C |} |} IN "BTerm" -->
   "vbind"{| <J> >- con_sequent_concl{"vbind"{| >- C |}} |}
   <-->
   "vbind"{| <J> >- "vbind"{| >- C |} |}
>>

(************************************************************************
 * Bsequent splitting.
 *
 * These reductions specify the form of the tuple produced by
 * bsequent.
 *
 * The hardest part is specifying that the conclusion is
 * the same, but at greater depth.
 *)
interactive_rw pre_sequent_concl : <:xrule<
   "vbind"{| >- "std_sequent"{| <J> >- C |} |} IN StdSequent{bdepth{"vbind"{| >- "ignore"{| <J> >- "dummy_bterm" |} |}}} -->
   "vbind"{| >- snd{"pre_sequent"{| <J> >- C |}} |}
   <-->
   "vbind"{| >- "vbind"{| <J> >- C |} |}
>>

interactive_rw bsequent_concl : <:xrule<
   arg IN BTerm{0} -->
   "sequent_wf"{| <J> >- C |} -->
   snd{snd{bsequent{arg}{| <J> >- C |}}}
   <-->
   "vbind"{| <J> >- C |}
>>

doc <:doc<
   Reduce the bsequent to a tuple.
>>
interactive_rw split_bsequent : <:xrule<
   arg IN BTerm{0} -->
   "sequent_wf"{| <J> >- C |} -->
   bsequent{arg}{| <J> >- C |}
   <-->
   "sequent"{arg; "hyplist"{| <J> |}; "vbind"{| <J> >- C |}}
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
