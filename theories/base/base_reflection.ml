doc <:doc<
   @begin[doc]
   @module[Base_reflection]

   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2004 MetaPRL Group

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

   Author: Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Shell_theory
extends Top_conversionals
doc docoff

open Basic_tactics

declare bterm
declare sequent_arg{'t}
declare term

(*
if_bterm{'bt; 'tt} evaluates to 'tt when 'bt is a well-formed bterm
operator and must fail to evaluate otherwise.

rewrite axiom: if_bterm{bterm{<H>; x:_; <J> >- x}; 'tt} <--> 'tt
ML rewrite axiom:
    if_bterm{bterm{<H> >- _op_{<J1>.t1, ..., <Jn>.tn}}; 'tt}
       <-->
    if_bterm{bterm{<H>; <J1> >- 't1};
       if_bterm{<H>; <J2> >- 't2};
          ...
            if_bterm{<H>; <Jn> >- 'tn}; 'tt}...}}
*)

declare if_bterm{'bt; 'tt}

prim_rw reduce_ifbterm1 {| reduce |} 'H :
   if_bterm{ sequent [bterm] { <H>; x: 't; <J> >- 'x }; 'tt } <--> 'tt

let bterm_arg = <<sequent_arg{bterm}>>

let hyp_of_var v =
   Hypothesis(v, <<term>>)

let make_bterm_sequent hyps goal =
   mk_sequent_term {
      sequent_args = bterm_arg;
      sequent_hyps = SeqHyp.of_list hyps;
      sequent_goals = SeqGoal.of_list [goal]
   }

let dest_bterm_sequent term =
   let seq = TermMan.explode_sequent term in
      if (SeqGoal.length seq.sequent_goals = 1) && alpha_equal seq.sequent_args bterm_arg then
         SeqHyp.to_list seq.sequent_hyps, (SeqGoal.get seq.sequent_goals 0)
      else raise (RefineError ("dest_bterm_sequent", StringTermError ("not a bterm sequent", term)))

ml_rw reduce_ifbterm2 (* {| reduce |} *) : ('goal :  if_bterm{ sequent[bterm]{ <H> >- 't}; 'tt }) =
   let bt, tt = two_subterms goal in
   let hyps, t = dest_bterm_sequent bt in
   let t' = dest_term (unquote_term t) in
   let rec wrap_if = function
      [] -> tt
    | s :: subterms ->
         let bt = dest_bterm s in
         let new_bterm = make_bterm_sequent (hyps @ (List.map hyp_of_var bt.bvars)) bt.bterm in
            <:con<if_bterm{$new_bterm$;$wrap_if subterms$}>>
   in wrap_if t'.term_terms

let resource reduce +=
   (<<if_bterm{ sequent[bterm]{ <H> >- 't}; 'tt }>>, reduce_ifbterm2)

