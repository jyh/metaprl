doc <:doc<
   @module[Czf_itt_inv_image]

   The @tt[Czf_itt_inv_image] module defines the @emph{inverse image}
   of a set under some mapping. The inverse image is defined as a set
   constructor $@invimage{x; s; t; a[x]}$. The term $s$ and $t$ must
   be sets, and $a[x]$ must be functional. The elements of the inverse
   image are the elements of $x$ in $s$ for which $a[x]$ in $t$ is true.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

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
extends Czf_itt_sep
doc docoff

open Lm_debug
open Lm_printf

open Tactic_type.Conversionals

open Dtactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc terms
declare inv_image{'s; x. 'a['x]; 't}
doc docoff

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   The @tt{inv_image} term is defined by separation.
>>
prim_rw unfold_inv_image: inv_image{'s; x. 'a['x]; 't} <-->
   sep{'s; x. mem{'a['x]; 't}}
doc docoff

let fold_inv_image = makeFoldC << inv_image{'s; x. 'a['x]; 't} >> unfold_inv_image

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform inv_image_df : parens :: except_mode[src] :: inv_image{'s; x. 'a; 't} =
   pushm[0] `"{" slot{'x} " " Mpsymbols!member `"s " slot{'s} mid slot{'a} " " Mpsymbols!member `"s " slot{'t} `"}" popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Well-formedness}

   The inverse image $@invimage{x; s; a[x]; t}$ is well-formed
   if $s$ and $t$ are sets, and $a[x]$ is functional.
>>
interactive inv_image_isset {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- isset{'t} } -->
   sequent { <H> >- fun_set{z. 'a['z]} } -->
   sequent { <H> >- isset{inv_image{'s; x. 'a['x]; 't}} }

doc <:doc<
   @modsubsection{Introduction}

   A set $y$ is a member of $@invimage{x; s; a[x]; t}$ if
   the inverse image is well-formed; if $@mem{y; s}$;
   and if $@mem{a[y]; t}$.
>>
interactive inv_image_intro {| intro [] |} :
   sequent { <H> >- isset{'y} } -->
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- isset{'t} } -->
   sequent { <H> >- fun_set{x. 'a['x]} } -->
   sequent { <H> >- mem{'y; 's} } -->
   sequent { <H> >- mem{'a['y]; 't} } -->
   sequent { <H> >- mem{'y; inv_image{'s; x. 'a['x]; 't}} }

doc <:doc<
   @modsubsection{Elimination}

   An assumption $@mem{y; @invimage{x; s; a[x]; t}}$ implies two facts:
   $@mem{y; s}$ and $@mem{a[y]; t}$.
>>
interactive inv_image_elim {| elim [] |} 'H :
   sequent { <H>; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; <J['x]> >- isset{'y} } -->
   sequent { <H>; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; <J['x]> >- isset{'s} } -->
   sequent { <H>; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; <J['x]> >- isset{'t} } -->
   sequent { <H>; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; <J['x]> >- fun_set{x. 'a['x]} } -->
   sequent { <H>; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; <J['x]>; v: mem{'y; 's}; w: mem{'a['y]; 't} >- 'C['x] } -->
   sequent { <H>; x: mem{'y; inv_image{'s; x. 'a['x]; 't}}; <J['x]> >- 'C['x] }
doc docoff

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
