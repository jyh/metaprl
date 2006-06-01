doc <:doc<
   @module[Itt_singleton]

   The @tt[Itt_singleton] module defines a singleton type.
   <<singleton{'a;'A}>> is a subtype of $A$ that contains $a$.
   It also contains all elements that are equal to $a$ in $A$ and only those elements.
   @em[Cf]. Section @hrefmodule[Itt_simple_singleton].
   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2003-2006 MetaPRL Group, Cornell University and
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

   Author:
    Alexei Kopylov @email{kopylov@cs.cornell.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_subtype
extends Itt_struct
extends Itt_set
extends Itt_logic
extends Itt_equal

doc docoff

open Lm_debug
open Lm_printf

open Dtactic

open Itt_equal

doc <:doc<
   @modsection{Definition}
   By definition <<singleton{'a;'A}>> is a subtype of $A$ that contain only one element $a$
   (and of course all elements equal to $a$).
>>

define singleton: singleton{'a;'A} <--> {x:'A | 'a='x in 'A}

doc docoff

dform singleton_df: singleton{'a;'A} = `"{" slot{'a} `"}" sub{'A}

doc <:doc<
   @modsection{Rules}
   Rules for singleton follow immediately from the definition.
>>

interactive singletonEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H> >- 'a1 = 'a2 in 'A1 } -->
   sequent { <H> >- singleton{'a1; 'A1} = singleton{ 'a2; 'A2 } in univ[i:l] }

interactive singleton_wf {| intro[] |}:
   sequent{ <H> >- 'a in 'A} -->
   sequent{ <H> >- "type"{singleton{'a;'A}} }

interactive singleton_intro {| intro[] |}:
   sequent{ <H> >- 'a = 'b in 'A} -->
   sequent{ <H> >- 'b in singleton{'a;'A} }

interactive singleton_elim {| elim[] |} 'H:
   sequent{ <H>; x : 'A; u: 'a='x in 'A; <J['x]> >- 'C['x] } -->
   sequent{ <H>; x : singleton{'a;'A}; <J['x]> >- 'C['x] }

interactive singleton_equal {| intro[] |}:
   sequent{ <H> >- 'b  in singleton{'a;'A}} -->
   sequent{ <H> >- 'c  in singleton{'a;'A}} -->
   sequent{ <H> >- 'b = 'c in singleton{'a;'A} }

let resource intro += (<<'b in singleton{'a;'A}>>, wrap_intro singleton_intro)

doc docoff
