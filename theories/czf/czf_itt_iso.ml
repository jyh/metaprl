doc <:doc<
   @begin[doc]
   @module[Czf_itt_iso]

   The @tt[Czf_itt_iso] module defines the isomorphism.
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
extends Czf_itt_hom
doc <:doc< @docoff >>

open Lm_debug
open Lm_printf

open Dtactic

let _ =
   show_loading "Loading Czf_itt_iso%t"

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< @doc{@terms} >>
declare iso{'g1; 'g2; x. 'f['x]}
doc <:doc< @docoff >>

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rewrites
   An isomorphism is a homomorphism that is one-to-one and onto G2.
   @end[doc]
>>
prim_rw unfold_iso : iso{'g1; 'g2; x. 'f['x]} <-->
   (hom{'g1; 'g2; x. 'f['x]} & (all c: set. all d: set. (mem{'c; car{'g1}} => mem{'d; car{'g1}} => eq{'f['c]; 'f['d]} => eq{'c; 'd})) & (all e: set. (mem{'e; car{'g2}} => (exst p: set. (mem{'p; car{'g1}} & eq{'e; 'f['p]})))))
doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform iso_df : parens :: except_mode[src] :: iso{'g1; 'g2; x. 'f} =
   `"iso(" slot{'g1} `"; " slot{'g2} `"; " slot{'f} `")"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @rules
   @modsubsection{Well-formedness}

   The proposition $@iso{x; g1; g2; f[x]}$ is well-formed
   if $g1$ and $g2$ are labels, and $f[x]$ is a set for any
   set argument $x$.
   @end[doc]
>>
interactive iso_type {| intro [] |} :
   sequent { <H> >- 'g1 IN label } -->
   sequent { <H> >- 'g2 IN label } -->
   sequent { <H>; x: set >- isset{'f['x]} } -->
   sequent { <H> >- "type"{iso{'g1; 'g2; x. 'f['x]}} }

doc <:doc<
   @begin[doc]
   @modsubsection{Functionality}

   The @tt{iso} judgment is functional in the function
   argument.
   @end[doc]
>>
interactive iso_fun {| intro [] |} :
   sequent { <H> >- 'g1 IN label } -->
   sequent { <H> >- 'g2 IN label } -->
   sequent { <H> >- group{'g1} } -->
   sequent { <H> >- group{'g2} } -->
   sequent { <H>; z: set; x1: set; y1: mem{'x1; car{'g1}} >- mem{'f['z; 'x1]; car{'g2}} } -->
   sequent { <H>; z: set >- fun_set{x. 'f['x; 'z]} } -->
   sequent { <H> >- fun_prop{z. iso{'g1; 'g2; y. 'f['z; 'y]}} }

doc <:doc< @docoff >>
(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
