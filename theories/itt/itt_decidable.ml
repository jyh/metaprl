doc <:doc<
   @begin[doc]
   @module[Itt_decidable]

   It is occasionally useful to assert the @emph{decidability}
   of a proposition $P$.  The proposition is decidable if
   $P @vee @not{P}$.  Decidable propositions allow reasoning
   by case analysis.

   The @tt{Itt_decidable} module defines a generic
   tactic @hreftactic[decideT] to help prove the decidability
   of propositions.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 1998 Jason Hickey, Cornell University

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
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_logic
doc <:doc< @docoff >>

open Lm_debug
open Lm_printf
open Tactic_type.Tacticals
open Dtactic
open Auto_tactic

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

let _ =
   show_loading "Loading Itt_decidable%t"

(************************************************************************
 * decidable                                                            *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @terms

   The definition of $@decidable{P}$ is $@or{P; @not{P}}$.
   @end[doc]
>>
define unfold_decidable : decidable{'p} <--> ( 'p or not {'p} )
doc <:doc< @docoff >>

dform decidable_df : except_mode[src] :: decidable{'p} = `"Decidable(" 'p `")"

interactive_rw fold_decidable : ( 'p or not {'p} ) <--> decidable{'p}

doc <:doc<
   @begin[doc]
   @rules

   The @tt{assert_decidable} rule allows case analysis
   over a decidable proposition $p$.
   @end[doc]
>>
interactive assert_decidable 'p :
   [decidable] sequent { <H> >- decidable {'p} } -->
   sequent { <H>; x: 'p >- 'G } -->
   sequent { <H>; x: not{'p} >- 'G } -->
   sequent { <H> >- 'G }

let decidable_term = <<decidable{'p}>>
let decidable_opname = opname_of_term decidable_term
let is_decidable_term = is_dep0_term decidable_opname
let mk_decidable_term = mk_dep0_term decidable_opname
let dest_decidable_term = dest_dep0_term decidable_opname

doc <:doc<
   @begin[doc]
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
   @end[doc]
>>
let decideT t =
   assert_decidable t thenLT [tcaT; idT; idT]

doc <:doc<
   @begin[doc]
   @modsubsection{Basic decidability}

   The propositions $@true$ and $@false$ are always decidable.
   @end[doc]
>>
interactive dec_false {| intro [] |} :
   sequent { <H> >- decidable{."false"} }

interactive dec_true {| intro [] |} :
   sequent { <H> >- decidable{."true"} }
doc <:doc< @docoff >>
