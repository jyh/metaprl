doc <:doc<
   @module[Itt_sqsimple]

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

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

   Authors:
    Alexei Kopylov @email{kopylov@cs.caltech.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>

extends Itt_logic
extends Itt_squiggle

open Basic_tactics
open Itt_equal
open Itt_struct

doc <:doc<
   @modsection{Definition}
   A type is said to be squiggle simple if only squiggle equal elements are equal in this type.
>>

define unfold_sqsimple: sqsimple{'T} <--> all x:'T. all y:'T. ('x='y in 'T => 'x~'y)

define unfold_sqsimple_type: sqsimple_type{'T} <--> "type"{'T} & sqsimple{'T}

doc <:doc<
   @modsection{Basic Rules}
>>

let resource intro +=
   [<<sqsimple{'T}>>, wrap_intro (rw unfold_sqsimple 0);
    <<"type"{sqsimple{'T}}>>, wrap_intro typeEquality;
    <<sqsimple_type{'T}>>, wrap_intro (rw unfold_sqsimple_type 0);
    <<"type"{sqsimple_type{'T}}>>, wrap_intro typeEquality
   ]


interactive sqsimple_elim  {| elim[ThinOption thinT] |} 'H:
      sequent{ <H>; sqsimple{'T}; <J> >- 'x = 'y in 'T } -->
      sequent{ <H>; sqsimple{'T}; <J> >- 'x ~ 'y }

interactive sqsimple_type_elim1 {| elim[ThinOption thinT] |} 'H:
      sequent{ <H>; sqsimple_type{'T}; <J> >- 'x = 'y in 'T } -->
      sequent{ <H>; sqsimple_type{'T}; <J> >- 'x ~ 'y }

interactive sqsimple_type_elim2 {| nth_hyp |} 'H:
      sequent{ <H>; sqsimple_type{'T}; <J> >- "type"{'T} }

interactive sqsimple 'T:
      sequent{ <H> >- sqsimple{'T} } -->
      sequent{ <H> >- 'x = 'y in 'T } -->
      sequent{ <H> >- 'x ~ 'y }

(* TODO: prove that basic types and operators are sqsimple (exept fun, top, //) *)
(* TODO: subset and subtype of sqsimple type is sqsimple. if X subtupe Y and Y is sqsimple => X subset Y *)


