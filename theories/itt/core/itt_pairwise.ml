doc <:doc<
   @module[Itt_pointwise]

   @parents
   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2004-2006 MetaPRL, California Institute of Technology

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

   Author: Alexei Kopylov @email{kopylov@cs.caltech.edu}
   @end[license]
>>

extends Itt_equal
extends Itt_squiggle

doc docoff

open Basic_tactics

open Itt_squiggle
open Itt_struct

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   The following rule is valid only for pairwise functionality.
   They are invalid in pointwise functionality and contradict, for example, to @hrefrule[quotientElimination2] rule.
>>

prim let_rule 'H (!x='s in 'S):
  [assertion] sequent { <H>; <J> >- 's in 'S } -->
   [main]    ('t['x; 'u]:  sequent { <H>; x: 'S;  <J>; u:'s ~ 'x  >- 'T } )-->
   sequent { <H>; <J>  >- 'T}
      = 't['s; it]

doc docoff

let rec onAllHypFrom n tac =  (* applies tac on all hyp betweeb n ending -1 excluded *)
    funT (fun p ->
       if n= -1 || n=Sequent.hyp_count p then idT else
       let next = if n>0 then n+1 else n-1 in
          tac next thenT onAllHypFrom next tac
         )

let letAtT i x_is_s_in_S =
   let i =
      if i < 0 then
         i + 1
      else
         i
   in
      let_rule i x_is_s_in_S thenMT (rwh (hypC (-1)) 0 thenT onAllHypFrom i (rwh (hypC (-1))) thenT thinT (-1))

doc <:doc<
      Using @rule[letAtT] rule, we can "split" a hypothesis.
      That is, we can copy a hypothesis and make conclusion and hypotheses
      after the new copy of it to be depend on this new copy.
      Cf. @tactic[copyHypT].
>>

interactive splitHyp 'H 'J:
   sequent { <H>; x: 'A;  <J['x]>; y:'A; <K['y]>  >- 'T['y] } -->
   sequent { <H>; x:'A; <J['x]>; <K['x]>  >- 'T['x]}

doc <:doc<
      The @tactic[spliHypT] $i$ $j$ tactic split $i$'th hypothesis and adds it to the $j$'s place.
      It is useful for elimination rules where we want to keep the original hypothesis intact.
      Cf. @tactic[splitHypT].
      @docoff
>>

let splitHypT i j = funT (fun p ->
   let i = get_pos_hyp_num p i in
   let j = if j < 0 then (get_pos_hyp_num p j) + 1 else j in
      if j > i then
         splitHyp i (j - i)
      else
         moveHypT i j thenT copyHypT j (i+1)
   )
