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
extends Meta_extensions_theory
extends Itt_hoas_sequent
extends Itt_match

doc docoff

open Basic_tactics

(*
 * Error term.
 *)
declare Invalid_argument

doc <:doc<
   A ``standard'' sequent is a << BTerm >> composed of hypotheses
   << shyp{'h; x. 'seq['x]} >> where << 'seq['x] >> must be
   a standard sequent, or a conclusion << sconcl{'c} >>.
>>
declare shyp{'h; x. 'rest['x]}
declare sconcl{'c}

doc docoff

define unfold_is_std_sequent : is_std_sequent{'e} <--> <:xterm<
   (fix f e ->
       dest_bterm e with
          l, r -> "bfalse"
        | d, o, s ->
             if is_same_op{o; $shyp{h; x. rest}} then
                f nth{s; 1}
             else
                is_same_op{o; $sconcl{e}}) e
>>

define unfold_StdSequent : StdSequent <--> { e: BTerm | "assert"{is_std_sequent{'e}} }

(*
 * A PreSequent is a sequent without the argument.
 *)
define unfold_is_pre_sequent_depth : is_pre_sequent{'i; 's} <--> <:xterm<
   let hyps, concl = s in
      hyp_depths{i; hyps} && bdepth{concl} = i +@ length{hyps} in "nat"
>>

define unfold_PreSequent_depth : PreSequent{'i} <--> <:xterm<
   { s: (list{"BTerm"} * "BTerm") | is_pre_sequent{i; s} }
>>

define unfold_PreSequent : PreSequent <--> PreSequent{0}

(*
 * Turn a Term_std-style sequent into a PreSequent.
 *)
define unfold_flatten_sequent : flatten_sequent{'e} <--> <:xterm<
   (fix f e ->
       dest_bterm e with
          l, r -> "Invalid_argument"
        | d, o, s ->
             if is_same_op{o; $shyp{h; x. rest}} then
                let hyps, concl = f nth{s; 1} in
                   (nth{s; 0} :: hyps, concl)
             else if is_same_op{o; $sconcl{e}} then
                ([], nth{s; 0})
             else
                "Invalid_argument") e
>>

(*
 * BUG: JYH: currently, we have no way to define sequent terms.
 * Use the prim_rw form instead.
 *)
doc <:doc<
   A ``BTerm'' sequent << bsequent{'arg}{| <H> >- 'C |} >> is first
   converted to a standard sequent, then flattened into a triple
   << ('arg, ('hyps, 'concl)) >>, where the << 'hyps >> are represented
   as a list of BTerms of increasing depth.
>>
declare sequent [std_sequent] { Term : Term >- Term } : Term

prim_rw unfold_std_sequent std_sequent{| <J> >- 'C |} : <:xrewrite<
   "std_sequent"{| <J> >- C |}
   <-->
   sequent_ind{u, v. $`shyp{u; x. $,happly{v; x}}; "TermSequent"{| <J> >- $`sconcl{C} |}}
>>

prim_rw unfold_bsequent : <:xrewrite<
   bsequent{arg}{| <J> >- C |}
   <-->
   let hyps, concl = flatten_sequent{"std_sequent"{| <J> >- C |}} in
      "sequent"{arg; hyps; concl}
>>

doc docoff

(************************************************************************
 * Standard sequents.
 *)

(*
 * Well-formedness of the standard-sequent predicate.
 *)
let fold_is_std_sequent = makeFoldC << is_std_sequent{'e} >> unfold_is_std_sequent

interactive_rw reduce_is_std_sequent : <:xrewrite<
   is_std_sequent{e}
   <-->
   dest_bterm e with
      l, r -> "bfalse"
    | d, o, s ->
         if is_same_op{o; $shyp{h; x. rest}} then
            is_std_sequent{nth{s; 1}}
         else
            is_same_op{o; $sconcl{e}}
>>

interactive_rw reduce_is_std_sequent_var {| reduce |} : <:xrewrite<
   l IN "nat" -->
   r IN "nat" -->
   is_std_sequent{var{l; r}}
   <-->
   "bfalse"
>>

interactive is_std_sequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "BTerm" -->
   <H> >- is_std_sequent{e} IN "bool"
>>

interactive wf_StdSequent {| intro [] |} : <:xrule<
   <H> >- "StdSequent" Type
>>

(*
 * Induction principle.
 *)
interactive elim_StdSequent {| elim [] |} 'H : <:xrule<
   "base" : <H>; e: "StdSequent"; <J[e]>; e1: "BTerm" >- C[$'[bdepth{e1}] sconcl{e1}] -->
   "step" : <H>; e: "StdSequent"; <J[e]>;
      e1: "BTerm"; e2: "StdSequent"; "bdepth"{e2} = "bdepth"{e1} +@ 1 in "nat"; C[e2]
      >- C[$'[bdepth{e1}] shyp{e1; x. $,subst{e2; x}}] -->
   <H>; e: "StdSequent"; <J[e]> >- C[e]
>>

(************************************************************************
 * Pre-sequents.
 *)

interactive is_pre_sequent_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- i IN "nat" -->
   "wf" : <H> >- s IN list{"BTerm"} * "BTerm" -->
   <H> >- is_pre_sequent{i; s} Type
>>

interactive wf1_PreSequent {| intro [] |} : <:xrule<
   "wf" : <H> >- i IN "nat" -->
   <H> >- PreSequent{i} Type
>>

interactive wf2_PreSequent {| intro [] |} : <:xrule<
   <H> >- "PreSequent" Type
>>

(*
 * Flattener rewrites.
 *)
let fold_flatten_sequent = makeFoldC << flatten_sequent{'e} >> unfold_flatten_sequent

interactive_rw reduce_flatten_sequent : <:xrewrite<
   flatten_sequent{e}
   <-->
   dest_bterm e with
       l, r -> "Invalid_argument"
     | d, o, s ->
          if is_same_op{o; $shyp{h; x. rest}} then
             let hyps, concl = flatten_sequent{nth{s; 1}} in
                (nth{s; 0} :: hyps, concl)
          else if is_same_op{o; $sconcl{e}} then
             ([], nth{s; 0})
          else
             "Invalid_argument"
>>

interactive_rw reduce_flatten_sequent_concl {| reduce |} : <:xrewrite<
   e IN "BTerm" -->
   bdepth{e} = d in "nat" -->
   flatten_sequent{$'[d] sconcl{e}}
   <-->
   ([], e)
>>

interactive_rw reduce_flatten_sequent_hyp {| reduce |} : <:xrewrite<
   e1 IN "BTerm" -->
   e2 IN "BTerm" -->
   bdepth{e2} = bdepth{e1} +@ 1 in "nat" -->
   flatten_sequent{mk_bterm{bdepth{e1}; $shyp{e1; x. e2}; [e1; e2]}}
   <-->
   let hyps, concl = flatten_sequent{e2} in
      (e1 :: hyps, concl)
>>

(*
 * Lemmas.
 *)
interactive is_pre_sequent_concl {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "BTerm" -->
   <H> >- is_pre_sequent{bdepth{e}; ([], e)}
>>

interactive concl_in_PreSequent {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "BTerm" -->
   <H> >- ([], e) IN PreSequent{bdepth{e}}
>>

interactive step_in_PreSequent {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "BTerm" -->
   "wf" : <H> >- s IN PreSequent{bdepth{e} +@ 1} -->
   <H> >- (let hyps, concl = s in (e :: hyps, concl)) IN PreSequent{bdepth{e}}
>>

(*
 * The flattener produces a flat sequent for any standard sequent.
 *)
interactive flatten_sequent_wf1 {| intro [] |} : <:xrule<
   "wf" : <H> >- e IN "StdSequent" -->
   <H> >- flatten_sequent{e} IN PreSequent{bdepth{e}}
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
