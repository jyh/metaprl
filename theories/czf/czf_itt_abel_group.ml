doc <:doc<
   @begin[doc]
   @module[Czf_itt_abel_group]

   The @tt[Czf_itt_abel_group] module defines abelian groups.
   A group is @emph{abelian} if its binary operation is
   commutative.

   @end[doc]

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

doc <:doc< @doc{@parents} >>
extends Czf_itt_group
doc <:doc< @docoff >>

open Lm_debug
open Lm_printf

open Dtactic

let _ =
   show_loading "Loading Czf_itt_abel_group%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< @doc{@terms} >>
declare abel{'g}
doc <:doc< @docoff >>

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rewrites

   A group $g$ is abelian if its operation is commutative.
   @end[doc]
>>
prim_rw unfold_abel: abel{'g} <-->
   (group{'g} & (all a: set. all b: set. (mem{'a; car{'g}} => mem{'b; car{'g}} => eq{op{'g; 'a; 'b}; op{'g; 'b; 'a}})))
doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform abel_df : except_mode[src] :: abel{'g} =
   `"abel(" slot{'g} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rules
   @modsubsection{Typehood}

   The @tt[abel] judgment is well-formed if its
   argument is a label.
   @end[doc]
>>
interactive abel_type {| intro [] |} :
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- "type"{abel{'g}} }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction}

   The proposition $@abel{g}$ is true if it is well-formed, $g$
   is a group, and @tt[op] is commutative.
   @end[doc]
>>
interactive abel_intro {| intro[] |} :
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- group{'g} } -->
   sequent { <H>; a: set; b: set; x: mem{'a; car{'g}}; y: mem{'b; car{'g}} >- eq{op{'g; 'a; 'b}; op{'g; 'b; 'a}} } -->
   sequent { <H> >- abel{'g} }
doc <:doc< @docoff >>

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
