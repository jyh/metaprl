doc <:doc<
   @module[Czf_itt_normal_subgroup]

   The @tt[Czf_itt_normal_subgroup] module defines normal subgroups.
   A subgroup $h$ of a group $g$ is @emph{normal} if its left and
   right cosets coincide, that is, if
   $$@forall a @in @car{g}. @equal{@lcoset{h; g; a}; @rcoset{h; g; a}}$$

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2002 Xin Yu, Caltech

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

   Author: Xin Yu
   @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Czf_itt_subgroup
extends Czf_itt_abel_group
extends Czf_itt_coset
doc docoff

open Lm_debug
open Lm_printf

open Dtactic

let _ =
   show_loading "Loading Czf_itt_normal_subgroup%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc terms
declare normal_subg{'s; 'g}
doc docoff

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   A subgroup $s$ of $g$ is normal if its left and right cosets coincides.
>>
prim_rw unfold_normal_subg : normal_subg{'s; 'g} <-->
   (subgroup{'s; 'g} & (all a: set. (mem{'a; car{'g}} => equal{lcoset{'s; 'g; 'a}; rcoset{'s; 'g; 'a}})))
doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform normal_subg_df : except_mode[src] :: normal_subg{'s; 'g} =
   `"normal_subgroup(" slot{'s} `"; " slot{'g} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Typehood}

   The @tt[normal_subg] judgment is well-formed if its
   arguments are labels.
>>
interactive normalSubg_wf {| intro [] |} :
   sequent { <H> >- 's IN label } -->
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- "type"{normal_subg{'s; 'g}} }

doc <:doc<
   @modsubsection{Introduction}

   The proposition $@normalsubg{s; g}$ is true if it is well-formed,
   $s$ is a subgroup of $g$, and for any $a$ in $@car{g}$,
   $@equal{@lcoset{s; g; a}; @rcoset{s; g; a}}$.
>>
interactive normalSubg_intro {| intro [] |} :
   sequent { <H> >- 's IN label } -->
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- subgroup{'s; 'g} } -->
   sequent { <H>; a: set; x: mem{'a; car{'g}} >- equal{lcoset{'s; 'g; 'a}; rcoset{'s; 'g; 'a}} } -->
   sequent { <H> >- normal_subg{'s; 'g} }

doc <:doc<
   @modsubsection{Theorems}

   All subgroups of abelian groups are normal.
>>
interactive abel_subg_normal 'H 's :
   sequent { <H>; x: abel{'g}; <J['x]> >- 's IN label } -->
   sequent { <H>; x: abel{'g}; <J['x]> >- 'g IN label } -->
   sequent { <H>; x: abel{'g}; <J['x]> >- subgroup{'s; 'g} } -->
   sequent { <H>; x: abel{'g}; <J['x]>; y: normal_subg{'s; 'g} >- 'C['x] } -->
   sequent { <H>; x: abel{'g}; <J['x]> >- 'C['x] }

doc docoff
let abelNormalSubgT t i = abel_subg_normal i t

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
