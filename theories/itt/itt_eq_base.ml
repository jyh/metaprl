doc <:doc<
   @begin[doc]
   @module[Itt_eq_base]

   The @tt[Itt_eq_base] module defines a $base$ type that allows turning
   squiggle equality into a first-class equality relation.
   @end[doc]

   For more information, see also the newsgroup thread at
   @url["news://news.metaprl.org/1ad4.3fd93890.24661%40news.metaprl.org"]
   (Message posted "Thu, 11 Dec 2003 19:39:59 -0800" by Aleksey Nogin
    with Subject ``Idea: "Base" type that solves a lot of problems'').

   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2004 MetaPRL group.

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

open Basic_tactics

doc <:doc<
   @begin[doc]
   @parents

   The following modules are needed to express the basic properties of the
   constructors presented here.
   @end[doc]
>>
extends Itt_equal
extends Itt_squiggle
extends Itt_esquash
extends Itt_bisect
extends Itt_subset

doc <:doc<
   @doc{
      The following modules are only needed to be able to prove extended properties
      of these constructors.
   }
>>
extends Itt_quotient
extends Itt_ext_equal
extends Itt_logic
extends Itt_antiquotient

doc "doc"{terms}
declare base
define unfold_base : base{'T} <--> 'T isect base
doc docoff

dform base_df : except_mode[src] :: base = `"Base"
dform base_op_df : except_mode[src] :: base{'T} =
   `"Base(" slot["no"]{'T} `")"

doc <:doc<
   @begin[doc]
   @rules
   @modsubsection{The $base$ type.}
   @end[doc]
>>

prim base_univ {| intro [] |} :
   sequent { <H> >- base in univ[i:l] } = it

interactive base_wf {| intro [] |} :
   sequent { <H> >- base Type }

prim base_sqeq {| nth_hyp |} :
   sequent { <H> >- esquash {'x = 'y in base} } -->
   sequent { <H> >- ('x ~ 'y) } = it

interactive_rw base_rw ('x ~ 'y) :
   esquash {'x = 'y in base} -->
   'x <--> 'y

prim base_eq :
   sequent { <H> >- ('x ~ 'y) } -->
   sequent { <H> >- esquash {'x = 'y in base} } = it

interactive base_top {| intro [] |} :
   sequent { <H> >- ext_equal {top; quot x,y:base // "true"} }

doc <:doc< @doc{@modsubsection{The properties of the $base{`""}$ type constructor}} >>

interactive base_op_wf {| intro [] |} :
   sequent { <H> >- 'T Type } -->
   sequent { <H> >- base{'T} Type }

interactive base_op_univ {| intro [] |} :
   sequent { <H> >- 'T in univ[i:l] } -->
   sequent { <H> >- base{'T} in univ[i:l] }

interactive base_subtype {| intro [] |} :
   sequent { <H> >- 'T Type } -->
   sequent { <H> >- base{'T} subtype base }

interactive base_subset {| intro [] |} :
   sequent { <H> >- 'T Type } -->
   sequent { <H> >- base{'T} subset base }

interactive base_op_eq {| intro [] |} :
   sequent { <H> >- 'T Type } -->
   sequent { <H> >- ext_equal{quot x,y:base{'T}//('x = 'y in 'T); 'T} }

doc docoff
