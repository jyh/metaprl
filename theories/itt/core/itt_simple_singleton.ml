doc <:doc<
   @module[Itt_simple_singleton]

   The @tt[Itt_simple_singleton] module defines a simple singleton type.
   The <<singleton{'a}>> has only one element $a$.
   The well-formedness rule has has the following restriction:
   we can say that <<singleton{'a}>> is a type only when $a$ is a constant.
   For example,
   $$   <<   sequent{  x:(quot u,v:bool//"true") >- "type"{singleton{'x}} }  >>$$
   is not true.

   Cf. Section @hrefmodule[Itt_singleton].
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
    Alexei Kopylov @email{kopylov@cs.caltech.edu}
    Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>
extends Itt_image2
extends Itt_unit
extends Itt_struct2
open Basic_tactics
open Base_rewrite
open Itt_squiggle
open Itt_equal

define unfold_singleton: singleton{'a} <--> Img{unit; x.'a}

doc docoff

dform singleton_df: singleton{'a} = `"{" slot{'a} `"}"



doc <:doc<
   @modsection{Rules}
>>

interactive singleton_univ {| intro [] |} :
   sequent { <H> >- singleton{'a<||>}  in univ[i:l] }

interactive singleton_wf {| intro[] |}:
   sequent{ <H> >- "type"{singleton{'a<||>}} }

interactive singleton_intro {| intro[] |}:
   sequent{ <H> >- 'a ~ 'b} -->
   sequent{ <H> >- 'b in singleton{'a<||>} }

interactive singleton_rw :
   sequent{ <H> >- 'x in singleton{'a} } -->
   sequent{ <H> >- 'x ~ 'a<||> }

let singletonC xa =
   rewriteC xa thenTC singleton_rw

interactive singleton_elim {| elim[] |} 'H:
   sequent{ <H>; <J['a]> >- 'C['a] } -->
   sequent{ <H>; x : singleton{'a<||>}; <J['x]> >- 'C['x] }

interactive singleton_equal {|  intro[] |}:
   sequent{ <H> >- 'b  in singleton{'a}} -->
   sequent{ <H> >- 'c  in singleton{'a}} -->
   sequent{ <H> >- 'b = 'c in singleton{'a<||>} }

let resource intro += (<<'b in singleton{'a<||>}>>, wrap_intro singleton_intro)

(* Are the following rules true?
interactive_rw singleton_rw ('x in singleton{'a}) :
   ('x in singleton{'a}) -->
   'x <--> 'a

interactive singleton_elim {| elim[] |} 'H:
   sequent{ <H>; <J['a]> >- 'C['a] } -->
   sequent{ <H>; x : singleton{'a}; <J['x]> >- 'C['x] }

interactive singleton_equal {| intro[] |}:
   sequent{ <H> >- 'b  in singleton{'a}} -->
   sequent{ <H> >- 'c  in singleton{'a}} -->
   sequent{ <H> >- 'b = 'c in singleton{'a} }
*)

doc <:doc<
   @modsection{Examples}
>>
extends Itt_dfun
extends Itt_bool
extends Itt_logic
extends Itt_quotient

doc <:doc<
 It is essential that we have the restriction that $a$ should be a constant to prove that
 <<singleton{'a}>> is a type.
 The judgment
    $$ sequent{  <H>; x:(quot u,v:bool//"true") >- "type"{singleton{'x}} } $$
 would lead to the contradiction.
>>

interactive singleton_contrexample :
   sequent{  <H>; x:(quot u,v:bool//"true") >- "type"{singleton{'x}} } -->
   sequent{  <H> >- "false" }

doc <:doc<
  However,
>>
interactive singleton_example :
   sequent{ <H>; x:bool >- "type"{singleton{'x}} }

doc <:doc<
  We can constuct $<<singleton{'a}>>$ even when $a$ is not reduced to a canonical form. E.g.,
>>
interactive singleton_example2 :
   sequent{ <H> >- ycomb in singleton{ycomb} }

