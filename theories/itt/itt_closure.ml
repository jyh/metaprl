doc <:doc<
   @begin[doc]
   @module[Itt_closure]

      If we have a function <<f:'T ->'T>> and a subset <<'X>> of <<'T>> then
      we can define a closure of <<'X>> as a set of all elements of $T$ that
      have the form $f(f(...f(x)..))$, where <<'x in 'X>>.

      More general, if we are given a set of @i{operators} <<'"Ф">>that map
      <<list{'T}>> to <<'T>> (i.e. operators of $T$ with arbitrary arity) then
      we can define a closure set <<Closure{'"Ф";'T}>> as a set of all elements
      of $T$ that can be constructed using operators from <<'"Ф">>.

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

   Authors:
    Alexei Kopylov @email{kopylov@cs.caltech.edu}

   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>

extends Itt_srec
extends Itt_functions
extends Itt_sqsimple
extends Itt_power
extends Itt_subset
extends Itt_record
extends Itt_bisect
extends Itt_list2
extends Itt_pairwise
extends Itt_pairwise2

doc docoff

open Basic_tactics
open Itt_struct


doc <:doc<
   @begin[doc]
   @modsection{Operators}
   An operator on $T$ is a function of an arbitrary arity on $T$.
   That is, an operator is define on a subset of <<list{'T}>> and range over $T$.
   We define <<Operators[i:l]{'T}>> as a collection of operators.
   @end[doc]
>>

define unfold_Operators: Operators[i:l]{'T} <-->
   {car: univ[i:l]; dom: ^car -> Power[i:l]{list{'T}};  f: op:(^car) -> ^dom ('op) -> 'T}

doc <:doc<
   @begin[doc]
    We will interpret <<'F>> from <<Operators[i:l]{'T}>> as the collection of
    operators $'F^f('op)$ for all <<'op>> from <<'F^car>>
    with the domain <<'F^car('op)>>.
   @end[doc]
>>

interactive operators_wf {| intro[] |} :
   sequent { <H> >- "type"{'T} } -->
   sequent { <H> >- "type"{Operators[i:l]{'T}} }

let resource elim += <<Operators[i:l]{'T}>>, fun n-> rw unfold_Operators n thenT dT n

let resource intro += <<'F in Operators[i:l]{'T}>>, wrap_intro (rw (addrC [0] unfold_Operators) 0 thenT dT 0)


doc <:doc<
   @begin[doc]
     A collection of operators <<'F>> could be wrapped into one function
      $$<<app{'F} in (op:('F^car) * ('F^dom ('op))) -> 'T>>$$
   @end[doc]
>>

define unfold_app: app{'F} <--> lambda{op_l. spread{'op_l; op,l. 'F^f 'op 'l }}

interactive_rw reduce_app {| reduce |}: app{'F} ('op,'l) <-->  'F^f 'op 'l

interactive app_wf {| intro[] |} univ[i:l]:
   sequent { <H> >- 'F in Operators[i:l]{'T}  } -->
   sequent { <H> >- app{'F} in  (op:('F^car) * ('F^dom ('op))) -> 'T  }


doc <:doc<
   @begin[doc]
   @modsubsection{Reversible Sets of Operators}
   @end[doc]
>>

define unfold_reverse: ReversibleOperators[i:l]{'F;  'T} <-->
   'F in Operators[i:l]{'T}
   & RReverse{app{'F}; op:('F^car) * ('F^dom ('op)); 'T}
   & sqsimple_type{'T}




doc <:doc<
   @begin[doc]
   @modsection{Closure}
   @end[doc]
>>


define unfold_Closure: Closure{'F; 'T} <-->
   srec{X. Img{ app{'F}; op:('F^car) * (list{'X} isect 'F^dom ('op)); 'T} }

let fold_Closure = makeFoldC <<Closure{'F; 'T}>>  unfold_Closure

interactive closure_wf {| intro[] |} univ[i:l]:
   sequent{ <H> >- "type"{'T} } -->
   sequent{ <H> >- 'F in Operators[i:l]{'T} } -->
   sequent{ <H> >- "type"{Closure{'F;'T}} }

interactive closure_subset {| intro[] |} univ[i:l]:
   sequent{ <H> >- 'F in Operators[i:l]{'T} } -->
   sequent{ <H> >- Closure{'F;'T} subset 'T }

interactive closure_elim {| elim[] |} 'H univ[i:l]:
   [wf] sequent{ <H>; x : Closure{'F;'T}; <J> >-  ReversibleOperators[i:l]{'F;  'T} } -->
   sequent{ <H>; <J>;
            op :'F^car;
            l: list{'T} isect 'F^dom('op);
            all_list{'l;x.'P['x]}
            >- 'P['F^f 'op 'l]
          } -->
   sequent{ <H>; x : Closure{'F;'T}; <J> >- 'P['x]}

interactive closure_intro {| intro[] |} univ[i:l]:
   [wf] sequent{ <H> >- "type"{'T} } -->
   [wf] sequent{ <H> >- 'F in Operators[i:l]{'T} } -->
   sequent{ <H> >- 'op in 'F^car } -->
   sequent{ <H> >- 'l in 'F^dom('op)  } -->
   sequent{ <H> >- 'l in list{ Closure{'F;'T} }  } -->
   sequent{ <H> >- 'F^f 'op 'l in Closure{'F;'T} }


(* TODO:

define n_ary{'n;'f} <-->

define constant{'c} <--> n_ary{'0;'c}


define unary{'f} <--> n_ary{'1;'f}

define binary{'f} <--> n_ary{'2;'f}

define Constants{'C;'T} <--> Img{c.constant{'c}; 'C; Operators{'T}}

lemma:  C subset T --> are_reversible{ Constats{'C;'T} }

*)
