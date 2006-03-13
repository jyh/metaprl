doc <:doc<
   @module[Itt_decidable]

   It is occasionally useful to assert the @emph{decidability}
   of a proposition $P$.  The proposition is decidable if
   $P @vee @not{P}$.  Decidable propositions allow reasoning
   by case analysis.

   The @tt{Itt_decidable} module defines a generic
   tactic @hreftactic[decideT] to help prove the decidability
   of propositions.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1999-2006 MetaPRL Group, Cornell University and
   California Institute of Technology

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

   Author: Aleksey Nogin @email{nogin@cs.cornell.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_logic
doc docoff

open Basic_tactics

(************************************************************************
 * decidable                                                            *
 ************************************************************************)

doc <:doc<
   @terms

   The definition of $@decidable{P}$ is $@or{P; @not{P}}$.
>>
define unfold_decidable : decidable{'p} <--> ( 'p or not {'p} )
doc docoff

dform decidable_df : except_mode[src] :: decidable{'p} = `"Decidable(" 'p `")"

interactive_rw fold_decidable : ( 'p or not {'p} ) <--> decidable{'p}

doc <:doc<
   @rules

   The @tt{assert_decidable} rule allows case analysis
   over a decidable proposition $p$.
>>
interactive assert_decidable 'p :
   [decidable] sequent { <H> >- decidable {'p} } -->
   sequent { <H>; x: 'p >- 'G } -->
   sequent { <H>; x: not{'p} >- 'G } -->
   sequent { <H> >- 'G }

doc docoff

let decidable_term = <<decidable{'p}>>
let decidable_opname = opname_of_term decidable_term
let is_decidable_term = is_dep0_term decidable_opname
let mk_decidable_term = mk_dep0_term decidable_opname
let dest_decidable_term = dest_dep0_term decidable_opname

doc <:doc<
   @tactics

   The @tactic[decideT] tactic applies the @hrefrule[assert_decidable]
   on a specific proposition $P$, then tries to eliminate the first subgoal.

   $$
   @rulebox{decideT; P;
     <<sequent{ <H> >- decidable{'P}}>>@cr
       <<sequent{ <H>; x: 'P >- 'C}>>@cr
       <<sequent{ <H>; x: not{'P} >- 'C}>>;
     <<sequent{ <H> >- 'C}>>}
   $$

   @docoff
>>
let decideT t =
   assert_decidable t thenLT [tcaT; idT; idT]

doc <:doc<
   @modsubsection{Basic decidability}

   The propositions $@true$ and $@false$ are always decidable.
>>
interactive dec_false {| intro [] |} :
   sequent { <H> >- decidable{"false"} }

interactive dec_true {| intro [] |} :
   sequent { <H> >- decidable{"true"} }

doc <:doc< Decidability can ignore the @tt[squash] operator >>

interactive dec_squash {| intro [] |} :
   [wf] sequent { <H> >- 'A Type } -->
   sequent { <H> >- decidable{'A} } -->
   sequent { <H> >- decidable{squash{'A}} }
doc docoff
