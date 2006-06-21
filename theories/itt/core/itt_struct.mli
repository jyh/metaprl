(*
 * Structural rules.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
 *
 * Copyright (C) 1998-2005 MetaPRL Group, Cornell University
 * and California Institute of Technology
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey <jyh@cs.cornell.edu>
 * Modified by: Aleksey Nogin <nogin@cs.cornell.edu>
 *
 *)

extends Itt_equal

open Basic_tactics

(*
 * H; x: A; J >- A ext x
 * by hypothesis
 *)
rule hypothesis 'H :
   sequent { <H>; x: 'A; <J['x]> >- 'A }

(*
 * H, x: A, J >- A ext t
 * by thin
 * H, J >- A ext t
 *)
rule thin 'H :
   sequent { <H>; <J> >- 'C } -->
   sequent { <H>; 'A; <J> >- 'C }

rule exchange 'H 'K 'L:
   sequent { <H>; <L>; <K>; <J> >- 'C } -->
   sequent { <H>; <K>; < L<|H|> >; <J> >- 'C }



(*
 * H, J >- T ext t[s]
 * by cut S
 * H, J >- S ext s
 * H, x: S, J >- T ext t[x]
 *)
rule cut 'H 'S :
   sequent { <H>; <J> >- 'S } -->
   sequent { <H>; 'S; <J> >- 'T } -->
   sequent { <H>; <J> >- 'T }

(*
 * H >- T
 * by introduction t
 * H >- t = t in T
 *)
rule introduction 't :
   sequent { <H> >- 't in 'T } -->
   sequent { <H> >- 'T }

(*
 * H >- T1[t1] ext t
 * by substitution (t1 = t2 in T2) lambda(x. T1[x])
 * H >- t1 = t2 in T2
 * H >- T1[t2]
 * H, x: T2 >- T1[x] = T1[x] in type
 *)
rule substitution ('t1 = 't2 in 'T2) bind{x. 'T1['x]} :
   sequent { <H> >- 't1 = 't2 in 'T2 } -->
   sequent { <H> >- 'T1['t2] } -->
   sequent { <H>; x: 'T2 >- "type"{'T1['x]} } -->
   sequent { <H> >- 'T1['t1] }

(*
 * H, x: A, J >- T
 * by hypothesesReplacement B
 * H, x:B, J >- T
 * H, x: A, J >- A = B in type
 *)
rule hypReplacement 'H 'B univ[i:l] :
   sequent { <H>; x: 'B; <J['x]> >- 'T['x] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'A = 'B<|H|> in univ[i:l] } -->
   sequent { <H>; x: 'A; <J['x]> >- 'T['x] }

(*
 * H; x: A[t1]; J[x] >> T1[x] ext t
 * by hypSubstitution (t1 = t2 in T2) bind(x. A[x])
 * H; x: A[t1]; J[x] >> t1 = t2 in T2
 * H; x: A[t2]; J[x] >> T1[x]
 * H, x: A[t1]; J[x]; z: T2 >> A[z] in type
 *)
rule hypSubstitution 'H ('t1 = 't2 in 'T2) bind{y. 'A['y]} :
   sequent { <H>; x: 'A['t1]; <J['x]> >- 't1 = 't2<|H|> in 'T2 } -->
   sequent { <H>; x: 'A['t2]; <J['x]> >- 'T1['x] } -->
   sequent { <H>; x: 'A['t1]; <J['x]>; z: 'T2 >- "type"{'A['z]} } -->
   sequent { <H>; x: 'A['t1]; <J['x]> >- 'T1['x] }

(*
 * Typehood.
 *)
rule equalityTypeIsType 'a 'b :
   sequent { <H> >- 'a = 'b in 'T } -->
   sequent { <H> >- "type"{'T} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval thinT : int -> tactic
topval thinAllT : int -> int -> tactic
topval thinDupT : tactic
topval nthAssumT : int -> tactic (* Does thinning to match against assumption *)
topval assertT : term -> tactic
topval dupHypT : int -> tactic
(* do not assert if already have the right conclusion *)
topval tryAssertT : term -> tactic -> tactic -> tactic
topval assertAtT : int -> term -> tactic
topval moveHypT : int -> int -> tactic
topval moveHypWithDependenciesThenT : int -> int -> (int->tactic) -> tactic
topval moveHypWithDependenciesT : int -> int -> tactic
topval copyHypT : int -> int -> tactic
topval dupT : tactic
topval useWitnessT : term -> tactic

topval forwardT : int -> tactic
topval forwardChainT : tactic

resource (term * (term -> int -> tactic), term -> int -> tactic) subst

topval substT : term -> int -> tactic
topval substConclT : term -> tactic
topval hypSubstT : int -> int -> tactic
topval revHypSubstT : int -> int -> tactic

topval replaceHypT : term -> int -> tactic

topval equalTypeT : term -> term -> tactic
topval memberTypeT : term -> tactic

val thinTermT : term -> tactic
val thinIfThinningT : int list -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
