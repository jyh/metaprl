doc <:doc< 
   @begin[doc]
   @module[Czf_itt_coset]
  
   The @tt[Czf_itt_coset] module defines the @emph{left coset}
   and the @emph{right coset}. If $h$ is a subgroup of $g$ and
   $@mem{a; @car{g}}$, then the left coset containing $a$ is
   $@{a * x | x @in @car{h}@}$ and the right coset containing $a$
   is $@{x * a| x @in @car{h}@}$. The elements of the left coset
   are those in $@car{g}$ which are equal to $@op{g; a; y}$ for
   some $y @in @car{h}$. The elements of the right coset are
   those in $@car{g}$ which are equal to $@op{g; y; a}$ for some
   $y @in @car{h}$. The cosets are defined by separation.
  
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
extends Czf_itt_dexists
extends Czf_itt_subgroup
doc <:doc< @docoff >>

open Lm_debug

open Dtactic

let _ =
   show_loading "Loading Czf_itt_coset%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< @doc{@terms} >>
declare lcoset{'h; 'g; 'a}
declare rcoset{'h; 'g; 'a}
doc <:doc< @docoff >>

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rewrites
  
   The @hrefterm[lcoset] and @hrefterm[rcoset] terms are defined by separation.
   @end[doc]
>>
prim_rw unfold_lcoset : lcoset{'h; 'g; 'a} <-->
   sep{car{'g}; x. "dexists"{car{'h}; y. eq{'x; op{'g; 'a; 'y}}}}

prim_rw unfold_rcoset : rcoset{'h; 'g; 'a} <-->
   sep{car{'g}; x. "dexists"{car{'h}; y. eq{'x; op{'g; 'y; 'a}}}}
doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform lcoset_df : parens :: except_mode[src] :: lcoset{'h; 'g; 'a} =
   `"lcoset(" slot{'h} `"; " slot{'g} `"; " slot{'a} `")"

dform rcoset_df : parens :: except_mode[src] :: rcoset{'h; 'g; 'a} =
   `"rcoset(" slot{'h} `"; " slot{'g} `"; " slot{'a} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Well-formedness}
  
   The $@lcoset{h; g; a}$ and $@rcoset{h; g; a}$ are well-formed
   if $h$ and $g$ are labels, and $a$ is a set.
   @end[doc]
>>
interactive lcoset_isset {| intro [] |} :
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- isset{'a} } -->
(*   sequent { <H> >- group{'g} } -->*)
   sequent { <H> >- isset{lcoset{'h; 'g; 'a}} }

interactive rcoset_isset {| intro [] |} :
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- isset{'a} } -->
(*   sequent { <H> >- group{'g} } -->*)
   sequent { <H> >- isset{rcoset{'h; 'g; 'a}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction}
  
   A set $x$ is a member of $@lcoset{h; g; a}$ if the
   left coset is well-formed, $@mem{a; @car{g}}$,
   $@mem{x; @car{g}}$, $@subgroup{h; g}$, and there
   exists a set $y$ such that $y$ is a member of
   $@car{h}$ and $x$ is equal to $@op{g; a; y}$
   in $@car{g}$. The case for @tt[rcoset] is similar.
   @end[doc]
>>
interactive lcoset_intro {| intro [] |} 'z :
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'x} } -->
   sequent { <H> >- isset{'z} } -->
   sequent { <H> >- mem{'a; car{'g}} } -->
   sequent { <H> >- mem{'x; car{'g}} } -->
   sequent { <H> >- subgroup{'h; 'g} } -->
   sequent { <H> >- mem{'z; car{'h}} } -->
   sequent { <H> >- eq{'x; op{'g; 'a; 'z}} } -->
   sequent { <H> >- mem{'x; lcoset{'h; 'g; 'a}} }

interactive rcoset_intro {| intro [] |} 'z :
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'x} } -->
   sequent { <H> >- isset{'z} } -->
   sequent { <H> >- mem{'a; car{'g}} } -->
   sequent { <H> >- mem{'x; car{'g}} } -->
   sequent { <H> >- subgroup{'h; 'g} } -->
   sequent { <H> >- mem{'z; car{'h}} } -->
   sequent { <H> >- eq{'x; op{'g; 'z; 'a}} } -->
   sequent { <H> >- mem{'x; rcoset{'h; 'g; 'a}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Elimination}
  
   The elimination form for the left coset
   $@mem{y; @lcoset{h; g; a}}$ implies $@mem{y; @car{g}}$ and
   also produces a witness $@mem{z; @car{h}}$ for which
   $@eq{y; @op{g; a; z}}$. The case for @tt[rcoset] is similar.
   @end[doc]
>>
interactive lcoset_elim {| elim [] |} 'H :
   sequent { <H>; x: mem{'y; lcoset{'h; 'g; 'a}}; <J['x]> >- 'h IN label } -->
   sequent { <H>; x: mem{'y; lcoset{'h; 'g; 'a}}; <J['x]> >- 'g IN label } -->
   sequent { <H>; x: mem{'y; lcoset{'h; 'g; 'a}}; <J['x]> >- isset{'a} } -->
   sequent { <H>; x: mem{'y; lcoset{'h; 'g; 'a}}; <J['x]> >- isset{'y} } -->
   sequent { <H>; x: mem{'y; lcoset{'h; 'g; 'a}}; <J['x]> >- mem{'a; car{'g}} } -->
   sequent { <H>; x: mem{'y; lcoset{'h; 'g; 'a}}; <J['x]> >- subgroup{'h; 'g} } -->
   sequent { <H>; x: mem{'y; lcoset{'h; 'g; 'a}}; <J['x]>; u: mem{'y; car{'g}}; z: set; v: mem{'z; car{'h}}; w: eq{'y; op{'g; 'a; 'z}} >- 'C['x] } -->
   sequent { <H>; x: mem{'y; lcoset{'h; 'g; 'a}}; <J['x]> >- 'C['x] }

interactive rcoset_elim {| elim [] |} 'H :
   sequent { <H>; x: mem{'y; rcoset{'h; 'g; 'a}}; <J['x]> >- 'h IN label } -->
   sequent { <H>; x: mem{'y; rcoset{'h; 'g; 'a}}; <J['x]> >- 'g IN label } -->
   sequent { <H>; x: mem{'y; rcoset{'h; 'g; 'a}}; <J['x]> >- isset{'a} } -->
   sequent { <H>; x: mem{'y; rcoset{'h; 'g; 'a}}; <J['x]> >- isset{'y} } -->
   sequent { <H>; x: mem{'y; rcoset{'h; 'g; 'a}}; <J['x]> >- mem{'a; car{'g}} } -->
   sequent { <H>; x: mem{'y; rcoset{'h; 'g; 'a}}; <J['x]> >- subgroup{'h; 'g} } -->
   sequent { <H>; x: mem{'y; rcoset{'h; 'g; 'a}}; <J['x]>; u: mem{'y; car{'g}}; z: set; v: mem{'z; car{'h}}; w: eq{'y; op{'g; 'z; 'a}} >- 'C['x] } -->
   sequent { <H>; x: mem{'y; rcoset{'h; 'g; 'a}}; <J['x]> >- 'C['x] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Theorems}
  
   If $h$ is a subgroup of group $g$, both the left and right
   cosets of $h$ containing $a$ are subsets of the carrier of
   $g$.
   @end[doc]
>>
interactive lcoset_subset {| intro [] |} :
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- mem{'a; car{'g}} } -->
   sequent { <H> >- subgroup{'h; 'g} } -->
   sequent { <H> >- \subset{lcoset{'h; 'g; 'a}; car{'g}} }

interactive rcoset_subset {| intro [] |} :
   sequent { <H> >- 'h IN label } -->
   sequent { <H> >- 'g IN label } -->
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- mem{'a; car{'g}} } -->
   sequent { <H> >- subgroup{'h; 'g} } -->
   sequent { <H> >- \subset{rcoset{'h; 'g; 'a}; car{'g}} }

doc <:doc< @docoff >>
(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
